;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.causality-cluster-test
  "The situation/causality cluster: situation, fluent, happening,
  uninterrupted_situation, static_situation, event (the state-of-affairs hierarchy under
  temporal), causal/acausal (whether a thing
  can occupy a cause slot), and causal_event/acausal_event defined via `intersection`.
  The tests hold that the cluster loads and that the `intersection`-defined kinds get
  their genls and membership from the CxCore intersection rules."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- believes?
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

;; ---- the state-of-affairs hierarchy loads --------------------------------

(tu/deftest-kb situation-hierarchy-holds
  (is (v/ask? kb (list 'genl 'static_situation 'situation) 'CxUniverse)
      "static_situation is a situation")
  (is (v/ask? kb (list 'genl 'event 'situation) 'CxUniverse)
      "event is a situation")
  (is (v/ask? kb (list 'genl 'event 'temporal) 'CxUniverse)
      "event is a temporal (transitively, via situation)")
  (testing "a static_situation is an uninterrupted fluent and an event an uninterrupted happening"
    (doseq [[k ups] '{static_situation [fluent uninterrupted]
                      event            [happening uninterrupted]
                      uninterrupted_situation [situation uninterrupted]}
            up ups]
      (is (true? (v/genl? kb k up 'CxUniverse)) (str k " genl " up))
      (is (true? (v/genl? kb k up 'CxLife)) (str k " genl " up " in CxLife")))))

(tu/deftest-kb a-situation-holds-or-happens-over-any-extent
  (doseq [ctx '[CxCore CxTime CxUniverse]]
    (testing (str ctx)
      (is (true? (v/genl? kb 'fluent 'situation ctx)))
      (is (true? (v/genl? kb 'happening 'situation ctx)))
      (is (true? (v/disjoint? kb 'fluent 'happening ctx)))))
  (testing "a situation denied being a fluent is a happening — the coverage half"
    (tu/with-terms [Fasting]
      (v/assert kb (list 'situation Fasting) 'CxUniverse)
      (v/assert kb (list 'not (list 'fluent Fasting)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'happening Fasting) 'CxUniverse)))))
  (testing "a situation denied being uninterrupted is intermittent, with no partition stated"
    (tu/with-terms [Treatment]
      (v/assert kb (list 'situation Treatment) 'CxUniverse)
      (v/assert kb (list 'not (list 'uninterrupted Treatment)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'intermittent Treatment) 'CxUniverse)))))
  (testing "an uninterrupted happening is an event, and an uninterrupted fluent a static_situation"
    (tu/with-terms [Kickoff Calm]
      (v/assert kb (list 'happening Kickoff) 'CxUniverse)
      (v/assert kb (list 'uninterrupted Kickoff) 'CxUniverse)
      (is (true? (v/ask? kb (list 'event Kickoff) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'uninterrupted_situation Kickoff) 'CxUniverse)))
      (v/assert kb (list 'fluent Calm) 'CxUniverse)
      (v/assert kb (list 'uninterrupted Calm) 'CxUniverse)
      (is (true? (v/ask? kb (list 'static_situation Calm) 'CxUniverse)))))
  (testing "an intermittent happening is no event"
    (tu/with-terms [WorldSeries]
      (v/assert kb (list 'happening WorldSeries) 'CxUniverse)
      (v/assert kb (list 'intermittent WorldSeries) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'event WorldSeries) 'CxUniverse)))))
  (testing "a situation, uninterrupted or not, may have a place"
    (is (true? (v/ask? kb '(orthogonal situation spatial) 'CxCore)))
    (is (true? (v/ask? kb '(orthogonal uninterrupted_situation spatial) 'CxCore))))
  (testing "a situation may be located in space and time, and a happening in some space"
    (is (true? (v/ask? kb '(orthogonal situation spatiotemporal) 'CxCore)))
    (is (true? (v/ask? kb '(orthogonal happening spatial) 'CxCore)))
    (is (= :orthogonal (v/subsumption-status kb 'happening 'spatial)))))

;; ---- a situation is no tangible -------------------------------------------

(tu/deftest-kb a-situation-is-not-the-matter-in-it
  ;; The boulder is an input to its rolling, not a part of it.
  (doseq [ctx '[CxCore CxUniverse]]
    (is (true? (v/disjoint? kb 'tangible 'situation ctx)) (str ctx))
    (is (true? (v/genl? kb 'situation 'intangible ctx)) (str "situation genl intangible in " ctx)))
  (tu/with-terms [Rolling]
    (v/assert kb (list 'event Rolling) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'stone Rolling) 'CxUniverse))
        "an event stated a stone is a clash")))

;; ---- causal / acausal partition of thing ---------------------------------

(tu/deftest-kb causal-and-acausal-are-kinds-of-thing
  (is (v/ask? kb (list 'genl 'causal 'thing) 'CxUniverse) "causal is a kind of thing")
  (is (v/ask? kb (list 'genl 'acausal 'thing) 'CxUniverse) "acausal is a kind of thing"))

(tu/deftest-kb a-cause-is-in-time-and-causal-and-acausal-cover-thing
  (is (true? (v/genl? kb 'causal 'temporal 'CxUniverse)) "a cause is in time")
  (testing "CxCore holds the partition, so CxTime reads causal without CxAbstract"
    (is (true? (v/genl? kb 'causal 'temporal 'CxTime)))
    (is (true? (v/disjoint? kb 'causal 'acausal 'CxTime))))
  (testing "what is in no time is no cause"
    (is (true? (v/disjoint? kb 'atemporal 'causal 'CxUniverse)))
    (is (true? (v/genl? kb 'atemporal 'acausal 'CxUniverse))))
  (testing "a thing denied being a cause is acausal — the coverage half"
    (tu/with-terms [Bystander]
      (v/assert kb (list 'thing Bystander) 'CxUniverse)
      (v/assert kb (list 'not (list 'causal Bystander)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'acausal Bystander) 'CxUniverse))))))

(tu/deftest-kb what-starts-or-stops-a-fluent-is-a-cause
  ;; initiates and terminates take a causal first argument; happens keeps temporal, since
  ;; something that happens need not cause anything.
  (doseq [p '[initiates terminates]]
    (is (true? (v/ask? kb (list 'arg p 1 'causal) 'CxTime)) (str p " takes a cause first"))
    (is (empty? (v/sentexes-matching kb (list 'arg p 1 'temporal) 'CxTime))
        (str p " declares its first position once")))
  (is (true? (v/ask? kb '(arg happens 1 temporal) 'CxTime))))

;; ---- causal_event / acausal_event get their genls from intersection ------

(tu/deftest-kb intersection-defined-events-derive-their-genls
  (is (v/ask? kb (list 'genl 'causal_event 'causal) 'CxUniverse)
      "the intersection rule makes causal_event a causal")
  (is (v/ask? kb (list 'genl 'causal_event 'event) 'CxUniverse)
      "the intersection rule makes causal_event an event")
  (is (v/ask? kb (list 'genl 'acausal_event 'acausal) 'CxUniverse)
      "the intersection rule makes acausal_event an acausal")
  (is (v/ask? kb (list 'genl 'acausal_event 'event) 'CxUniverse)
      "the intersection rule makes acausal_event an event"))

;; ---- membership: a causal event is a causal_event ------------------------

(tu/deftest-kb a-causal-event-instance-is-a-causal-event
  (tu/with-terms [Occurrence]
    (v/assert kb (list 'causal 'Occurrence) 'CxUniverse)
    (v/assert kb (list 'event 'Occurrence) 'CxUniverse)
    (is (believes? kb (list 'causal_event 'Occurrence) 'CxUniverse)
        "something both causal and an event is concluded a causal_event")))

(tu/deftest-kb an-acausal-non-event-is-not-a-causal-event
  (tu/with-terms [Record]
    (v/assert kb (list 'acausal 'Record) 'CxUniverse)
    (is (not (believes? kb (list 'causal_event 'Record) 'CxUniverse))
        "an acausal thing that is not an event is not a causal_event")))

;; ---- the divisions are declared disjoint ---------------------------------

(tu/deftest-kb causal-and-acausal-are-disjoint
  (is (v/disjoint? kb 'causal 'acausal 'CxUniverse)
      "a thing either can occupy a cause slot or cannot — the two sides do not overlap"))

(tu/deftest-kb a-situation-is-static-or-changing-but-not-both
  (is (v/disjoint? kb 'static_situation 'event 'CxUniverse)
      "the specialization axis of situation is a partition"))

(tu/deftest-kb causal-event-and-acausal-event-inherit-the-disjointness
  ;; causal_event genl causal and acausal_event genl acausal (from the intersection
  ;; rules), and causal is disjoint from acausal — so the two event kinds are disjoint by
  ;; the genl closure of disjointness, with no separate declaration.
  (is (= :disjoint (v/subsumption-status kb 'causal_event 'acausal_event))
      "disjointness reaches the intersection-defined kinds through their genls"))

(tu/deftest-kb a-single-thing-cannot-be-both-causal-and-acausal
  (tu/with-terms [Thing]
    (v/assert kb (list 'causal 'Thing) 'CxUniverse)
    (is (some? (v/handle-of kb (list 'causal 'Thing) 'CxUniverse)) "the first membership holds")
    (is (tu/stored-in-clash? kb (list 'acausal 'Thing) 'CxUniverse)
        "the disjoint membership is stored as a contradiction the settle weighs")))

;; ---- what has mass can be a cause ----------------------------------------

(tu/deftest-kb a-tangible-is-causal
  ;; the rock dented the car: anything with mass can fill a cause slot
  (is (v/ask? kb (list 'genl 'tangible 'causal) 'CxUniverse)
      "tangible is a kind of causal")
  (tu/with-terms [Rock]
    (v/assert kb (list 'stone 'Rock) 'CxUniverse)
    (is (v/ask? kb (list 'causal 'Rock) 'CxUniverse)
        "a rock, a tangible through stone and substance, reads causal")))

(tu/deftest-kb a-tangible-cannot-be-acausal
  ;; tangible below causal, and causal disjoint from acausal: the genl closure of
  ;; disjointness separates tangible from acausal with no separate declaration
  (is (v/disjoint? kb 'tangible 'acausal 'CxUniverse)
      "nothing with mass is acausal")
  (is (= :disjoint (v/subsumption-status kb 'tangible 'acausal))
      "the audit reads the pair disjoint"))

;; ---- a body of people can be a cause --------------------------------------

(tu/deftest-kb an-organization-is-causal
  ;; a company hires; a court rules
  (is (v/ask? kb (list 'genl 'organization 'causal) 'CxUniverse)
      "organization is a kind of causal")
  (tu/with-terms [Acme]
    (v/assert kb (list 'organization 'Acme) 'CxUniverse)
    (is (v/ask? kb (list 'causal 'Acme) 'CxUniverse)
        "an organization reads causal")))

;; ---- doneBy / performedBy: an event's doer --------------------------------
;; performedBy specializes doneBy through a predicate genl edge, so every performing is a
;; doing and not the other way round.  The doer position declares no type: a machine or
;; a process can bring an event about as well as a person can.

(tu/deftest-kb done-by-and-performed-by-are-declared-binary-instance-relations
  (doseq [p '[doneBy performedBy]]
    (testing (str p)
      (is (v/ask? kb (list 'binary_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'instance_relation_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'arg p 1 'event) 'CxUniverse) "the first position is the event")
      (is (empty? (v/sentexes-matching kb (list 'arg p 2 '?t) '?ctx)) "and the doer position declares no type")))
  (is (v/ask? kb '(genl performedBy doneBy) 'CxUniverse)
      "performedBy specializes doneBy"))

(tu/deftest-kb every-performing-is-a-doing
  (tu/with-terms [Launch Operator Spill Pump]
    (v/assert kb (list 'performedBy Launch Operator) 'CxUniverse)
    (is (v/ask? kb (list 'doneBy Launch Operator) 'CxUniverse)
        "the genl edge carries a performedBy tuple up to doneBy")
    (v/assert kb (list 'doneBy Spill Pump) 'CxUniverse)
    (is (not (v/ask? kb (list 'performedBy Spill Pump) 'CxUniverse))
        "and a doing is not concluded a performing")))

(tu/deftest-kb the-event-position-is-typed-and-the-doer-position-admits-any-term
  ;; Pinned to the constraint-only reading: `check` reports the position-1 conviction
  ;; there, and the entailing reading derives (event Stillness) instead.
  (tu/without-entailing
   (tu/with-terms [Stillness Flood Pump Drizzle]
     (v/assert kb (list 'static_situation Stillness) 'CxUniverse)
     (v/assert kb (list 'machine Pump) 'CxUniverse)
     (let [ps (v/check kb (list 'doneBy Stillness Pump) 'CxUniverse)
           p  (first (filter #(= :arg-type (:type %)) ps))]
       (is (some? p) "a static situation is not an event, so it cannot be done")
       (is (= 1 (:position p)))
       (is (= 'event (:expected p))))
     (testing "the constraint reaches performedBy through the genl edge"
       (is (some #(= :arg-type (:type %))
                 (v/check kb (list 'performedBy Stillness Pump) 'CxUniverse))))
     (v/assert kb (list 'event Flood) 'CxUniverse)
     (is (= [] (v/check kb (list 'doneBy Flood Pump) 'CxUniverse))
         "a machine can do an event")
     (v/assert kb (list 'event Drizzle) 'CxUniverse)
     (is (= [] (v/check kb (list 'doneBy Flood Drizzle) 'CxUniverse))
         "and so can another event"))))

;; ---- output: what an event left behind --------------------------------------
;; Each relation takes the event first.  tangibleOutput and intangibleOutput specialize
;; output by the kind of thing left behind.  Two rules conclude made from a tangible
;; output and a doer: an event someone intentionally initiated makes its output, and an
;; event a made thing did makes its output.  Growth is never intentionally initiated, so
;; a calf is not made by its mother.

(tu/deftest-kb the-output-relations-are-declared-event-first
  ;; output's second position holds a term of any kind and declares no type
  (doseq [[p t] '[[output nil] [tangibleOutput tangible] [intangibleOutput intangible]]]
    (testing (str p)
      (is (v/ask? kb (list 'binary_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'instance_relation_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'arg p 1 'event) 'CxUniverse) "the event is first")
      (if t
        (is (v/ask? kb (list 'arg p 2 t) 'CxUniverse) "and what it left behind second")
        (is (empty? (v/sentexes-matching kb (list 'arg p 2 '?t) '?ctx))))
      (is (seq (v/sentexes-matching kb (list 'comment p '?text) 'CxAbstract)))))
  (is (v/ask? kb '(genl tangibleOutput output) 'CxUniverse))
  (is (v/ask? kb '(genl intangibleOutput output) 'CxUniverse)))

(tu/deftest-kb a-tangible-or-intangible-output-is-an-output
  (tu/with-terms [Sawing1 Sawdust1 Run1 File1]
    (v/assert kb (list 'event Sawing1) 'CxUniverse)
    (v/assert kb (list 'tangibleOutput Sawing1 Sawdust1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'output Sawing1 Sawdust1) 'CxUniverse)))
    (v/assert kb (list 'event Run1) 'CxUniverse)
    (v/assert kb (list 'intangibleOutput Run1 File1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'output Run1 File1) 'CxUniverse)))))

(tu/deftest-kb the-second-position-says-which-kind-of-output
  ;; Pinned to the constraint-only reading, where `check` reports the conviction.
  (tu/without-entailing
   (tu/with-terms [Smelting1 Steel1 Run1 File1]
     (v/assert kb (list 'event Smelting1) 'CxUniverse)
     (v/assert kb (list 'substance Steel1) 'CxUniverse)
     (v/assert kb (list 'event Run1) 'CxUniverse)
     (v/assert kb (list 'intangible File1) 'CxUniverse)
     (let [p (first (filter #(= :arg-type (:type %))
                            (v/check kb (list 'intangibleOutput Smelting1 Steel1) 'CxUniverse)))]
       (is (some? p) "a tangible is not an intangible output")
       (is (= 2 (:position p))))
     (let [p (first (filter #(= :arg-type (:type %))
                            (v/check kb (list 'tangibleOutput Run1 File1) 'CxUniverse)))]
       (is (some? p) "nor an intangible a tangible one")
       (is (= 2 (:position p))))
     (is (= [] (v/check kb (list 'tangibleOutput Smelting1 Steel1) 'CxUniverse))))))

(tu/deftest-kb a-cloned-sheep-is-made-and-biological
  (tu/with-terms [Dolly1 Cloning1 Lab1]
    (v/assert kb (list 'sheep Dolly1) 'CxUniverse)
    (v/assert kb (list 'event Cloning1) 'CxUniverse)
    (v/assert kb (list 'tangibleOutput Cloning1 Dolly1) 'CxUniverse)
    (v/assert kb (list 'performedBy Cloning1 Lab1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'made Dolly1) 'CxUniverse))
        "an intentionally initiated event makes its output")
    (is (true? (v/ask? kb (list 'biological Dolly1) 'CxUniverse)))
    (is (not (tu/stored-in-clash? kb (list 'made Dolly1) 'CxUniverse))
        "made and biological at once is no clash")))

(tu/deftest-kb a-widget-a-made-machine-stamped-is-made
  (tu/with-terms [Machine1 Widget1 Stamping1]
    (v/assert kb (list 'machine Machine1) 'CxUniverse)
    (v/assert kb (list 'event Stamping1) 'CxUniverse)
    (v/assert kb (list 'tangibleOutput Stamping1 Widget1) 'CxUniverse)
    (v/assert kb (list 'doneBy Stamping1 Machine1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'made Machine1) 'CxUniverse)) "a machine is made")
    (is (true? (v/ask? kb (list 'made Widget1) 'CxUniverse))
        "and what a made thing does makes its output")))

(tu/deftest-kb what-a-natural-thing-merely-does-is-not-made
  ;; A calf is the output of its growth, which its mother did and nobody performed.
  (tu/with-terms [Calf1 Growth1 Cow1 WildSheep1]
    (v/assert kb (list 'cow Cow1) 'CxUniverse)
    (v/assert kb (list 'natural Cow1) 'CxUniverse)
    (v/assert kb (list 'event Growth1) 'CxUniverse)
    (v/assert kb (list 'tangibleOutput Growth1 Calf1) 'CxUniverse)
    (v/assert kb (list 'doneBy Growth1 Cow1) 'CxUniverse)
    (is (not (v/ask? kb (list 'made Calf1) 'CxUniverse)))
    (testing "and a wild sheep stated natural is no clash and not made"
      (v/assert kb (list 'sheep WildSheep1) 'CxUniverse)
      (is (not (tu/stored-in-clash? kb (list 'natural WildSheep1) 'CxUniverse)))
      (is (not (v/ask? kb (list 'made WildSheep1) 'CxUniverse))))))

(tu/deftest-kb an-output-of-a-performed-event-clashes-with-natural
  (tu/with-terms [Statue1 Carving1 Sculptor1]
    (v/assert kb (list 'event Carving1) 'CxUniverse)
    (v/assert kb (list 'performedBy Carving1 Sculptor1) 'CxUniverse)
    (v/assert kb (list 'tangibleOutput Carving1 Statue1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'made Statue1) 'CxUniverse)))
    (is (true? (tu/stored-in-clash? kb (list 'natural Statue1) 'CxUniverse))
        "the derived made meets a stated natural across the partition")))

(tu/deftest-kb the-input-relations-are-declared-event-first
  (doseq [p '[input destroyedInput preservedInput]]
    (testing (str p)
      (is (v/ask? kb (list 'binary_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'instance_relation_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'arg p 1 'event) 'CxUniverse) "the event is first")
      (is (empty? (v/sentexes-matching kb (list 'arg p 2 '?t) '?ctx))
          "and what went into it, second, declares no type")
      (is (seq (v/sentexes-matching kb (list 'comment p '?text) 'CxAbstract)))))
  (is (v/ask? kb '(genl destroyedInput input) 'CxUniverse))
  (is (v/ask? kb '(genl preservedInput input) 'CxUniverse))
  (is (seq (v/sentexes-matching kb '(termsRelated input output) 'CxAbstract))))

(tu/deftest-kb an-input-is-stored-and-its-first-position-is-an-event
  ;; Pinned to the constraint-only reading, where `check` reports the conviction.
  (tu/without-entailing
   (tu/with-terms [Sawing1 Plank1 Stillness1]
     (v/assert kb (list 'event Sawing1) 'CxUniverse)
     (is (not (tu/stored-in-clash? kb (list 'input Sawing1 Plank1) 'CxUniverse)))
     (is (true? (v/ask? kb (list 'input Sawing1 Plank1) 'CxUniverse)))
     (v/assert kb (list 'static_situation Stillness1) 'CxUniverse)
     (let [p (first (filter #(= :arg-type (:type %))
                            (v/check kb (list 'input Stillness1 Plank1) 'CxUniverse)))]
       (is (some? p) "a static situation is not an event, so nothing goes into it")
       (is (= 1 (:position p)))))))

(tu/deftest-kb a-destroyed-input-is-an-input
  (tu/with-terms [Smelting1 Ore1]
    (v/assert kb (list 'event Smelting1) 'CxUniverse)
    (v/assert kb (list 'destroyedInput Smelting1 Ore1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'input Smelting1 Ore1) 'CxUniverse)))))

(tu/deftest-kb a-three-place-use-of-an-event-relation-is-held-out
  ;; The arity check holds out a three-place fact only where binary_predicate is
  ;; stated.  The genl edge from instance_relation_predicate does not reach the check, so
  ;; each relation states binary_predicate.
  (doseq [p '[doneBy performedBy input destroyedInput preservedInput output tangibleOutput intangibleOutput]]
    (tu/with-terms [E1 X1 Y1]
      (v/assert kb (list p E1 X1 Y1) 'CxUniverse)
      (is (not (v/ask? kb (list p E1 X1 Y1) 'CxUniverse))
          (str "a three-place " p " is not believed")))))

;; ---- causes: a causal cause, a situation effect --------------------------

(tu/deftest-kb causes-is-declared-over-a-causal-cause-and-a-situation-effect
  (is (true? (v/ask? kb '(arg causes 1 causal) 'CxUniverse)) "the cause slot takes a causal thing")
  (is (true? (v/ask? kb '(arg causes 2 situation) 'CxUniverse)) "the effect slot takes a situation")
  (is (true? (boolean (v/isa? kb 'causes 'transitive))) "a chain of causes is itself a cause")
  (is (true? (boolean (v/isa? kb 'causes 'instance_relation_predicate))) "causes relates individuals")
  (is (seq (v/sentexes-matching kb '(comment causes ?c) 'CxAbstract))))

(tu/deftest-kb a-causal-event-causes-a-situation
  (tu/with-terms [Spark Blaze Ember]
    (v/assert kb (list 'causal_event Spark) 'CxUniverse)
    (v/assert kb (list 'causal_event Blaze) 'CxUniverse)
    (v/assert kb (list 'static_situation Ember) 'CxUniverse)
    (is (empty? (filter #(#{:arg-type} (:type %)) (v/check kb (list 'causes Spark Blaze) 'CxUniverse)))
        "a causal event in the cause slot and an event in the effect slot pass the check")
    (v/assert kb (list 'causes Spark Blaze) 'CxUniverse)
    (v/assert kb (list 'causes Blaze Ember) 'CxUniverse)
    (is (true? (v/ask? kb (list 'causes Spark Blaze) 'CxUniverse)) "the causation is believed")
    (is (true? (v/ask? kb (list 'causes Spark Ember) 'CxUniverse))
        "a chain of causes is itself a cause")))

(tu/deftest-kb an-acausal-cause-clashes-with-the-causal-membership-the-slot-derives
  ;; The cause slot derives `(causal Receipt)` beside the stated `(acausal_event Receipt)`,
  ;; and `(partition thing causal acausal)` places the clash between the two.
  (tu/with-terms [Receipt Blaze]
    (v/assert kb (list 'acausal_event Receipt) 'CxUniverse)
    (v/assert kb (list 'situation Blaze) 'CxUniverse)
    (v/assert kb (list 'causes Receipt Blaze) 'CxUniverse)
    (let [causal (v/handle-of kb (list 'causal Receipt) 'CxUniverse)]
      (is (some? causal))
      (is (some #(= #{causal (v/handle-of kb (list 'acausal_event Receipt) 'CxUniverse)}
                    (:nogood %))
                (v/contradictions kb))))))
