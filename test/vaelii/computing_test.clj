;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.computing-test
  "The computing vocabulary of CxTra: the relations over software tools, their invocations
  and receipts, media resources and network names, shipped in the opt-in theory CxTra
  below CxUniverse.  CxWell does not see the theory, so a context below CxWell reads no
  computing relation, and a user's own context opts in by placing itself under CxTra.

  The eleven relations, their argument declarations and the sixteen kinds the relations
  are typed over are all stated in CxTra, so a context reads a kind's `genl` edges and
  its disjointness only where it sees the theory: CxUniverse and CxWell read none.
  One default rule reads a causal agent's `hasCapability` from its tools; no rule
  concludes an invocation causal or acausal from its tool."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private binary-relations
  '[toolName toolInvoked resourceUrl receipt probesPredicate dnsResolvesTo agentHasTool
    toolEnablesCapability])

(def ^:private ternary-relations
  '[toolInvocationArg toolArgType toolArgComment])

(def ^:private kinds
  '[computational_system software_tool command_line_tool mcp_tool read_only_software_tool
    write_capable_software_tool information digital_artifact media_resource
    image video tool_invocation tool_receipt ip_address ipv4_address ipv6_address])

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(defn- declared-positions
  "The count of `arg` and `quotedArg` declarations of `p` that `ctx` reads."
  [p ctx]
  (+ (count (v/ask tu/*kb* (list 'arg p '?n '?t) ctx))
     (count (v/ask tu/*kb* (list 'quotedArg p '?n '?t) ctx))))

(defn- problem-types
  "The `:type` of each problem `check` reports for `sentence` in `ctx`, or of the argument
  conviction `assert` holds it inert under, under the constraint-only reading of the
  argument declarations."
  [sentence ctx]
  (tu/without-entailing
   (or (not-empty (mapv :type (v/check tu/*kb* sentence ctx)))
       (into [] (keep :type) [(tu/write-conviction tu/*kb* sentence ctx)]))))

(tu/deftest-kb the-theory-is-opt-in-below-cxuniverse
  (testing "the theory sees the upper ontology through CxUniverse"
    (is (tu/holds-sees CPT 'CxUniverse)))
  (testing "CxUniverse states the theory's context membership beside the other shipped contexts"
    (is (some #(v/premise? kb (:id %))
              (v/sentexes-matching kb (list 'context CPT) 'CxUniverse))))
  (testing "neither CxWell nor the upper ontology sees the theory"
    (is (not (tu/holds-sees 'CxWell CPT)))
    (is (not (tu/holds-sees 'CxUniverse CPT)))))

(tu/deftest-kb the-theory-declares-every-relation-and-comments-it-once
  (doseq [p binary-relations]
    (is (tu/holds-ask (list 'binary_predicate p) CPT) (str p " is binary in the theory")))
  (doseq [p ternary-relations]
    (is (tu/holds-ask (list 'ternary_predicate p) CPT) (str p " is ternary in the theory")))
  (doseq [p (concat binary-relations ternary-relations)]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment p '?c) CPT)))
        (str p " carries one comment in the theory"))
    (is (pos? (declared-positions p CPT)) (str p " declares a position in the theory"))))

(tu/deftest-kb the-kinds-are-stated-in-the-theory-with-one-comment-each
  (doseq [k kinds]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment k '?c) CPT)))
        (str k " carries one comment in the theory"))
    (is (empty? (v/sentexes-matching kb (list 'comment k '?c) 'CxUniverse))
        (str k " carries no comment in CxUniverse"))
    (is (tu/holds-genl k 'thing CPT) (str k " reaches thing from the theory")))
  (testing "the placements"
    (is (tu/holds-genl 'software_tool 'computational_system CPT))
    (is (tu/holds-genl 'computational_system 'intangible CPT))
    (is (tu/holds-genl 'read_only_software_tool 'acausal CPT))
    (is (tu/holds-genl 'write_capable_software_tool 'causal CPT))
    (is (tu/holds-genl 'tool_receipt 'acausal_event CPT))
    (is (tu/holds-genl 'tool_invocation 'event CPT))
    (is (tu/holds-genl 'ipv4_address 'ip_address CPT))
    (is (tu/holds-genl 'ipv6_address 'ip_address CPT))
    (is (tu/holds-genl 'ip_address 'string CPT)))
  (testing "the separations"
    (is (v/disjoint? kb 'read_only_software_tool 'write_capable_software_tool CPT))
    (is (v/disjoint? kb 'computational_system 'event CPT))
    (is (v/disjoint? kb 'computational_system 'expression CPT))
    (is (v/disjoint? kb 'tool_receipt 'tool_invocation CPT))
    (is (v/disjoint? kb 'image 'video CPT))
    (is (v/disjoint? kb 'ipv4_address 'ipv6_address CPT))))

(tu/deftest-kb a-context-under-the-theory-derives-the-declared-argument-types
  (tu/with-terms [CxDesk Grep Remove CallOne CallTwo Slip Clip]
    (v/assert kb (list 'genlCx CxDesk 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDesk CPT) 'CxUniverse)
    (tu/with-entailing
      (v/assert kb (list 'read_only_software_tool Grep) CxDesk)
      (v/assert kb (list 'write_capable_software_tool Remove) CxDesk)
      (v/assert kb (list 'toolInvoked CallOne Grep) CxDesk)
      (v/assert kb (list 'toolInvoked CallTwo Remove) CxDesk)
      (v/assert kb (list 'receipt CallOne Slip) CxDesk)
      (v/assert kb (list 'resourceUrl Clip "https://example.org/clip") CxDesk))
    (testing "a read-only tool is acausal and a write-capable tool is causal"
      (is (v/isa? kb Grep 'acausal CxDesk))
      (is (v/isa? kb Remove 'causal CxDesk))
      (is (v/isa? kb Grep 'intangible CxDesk)))
    (testing "the first argument of toolInvoked is derived a tool_invocation"
      (doseq [call [CallOne CallTwo]]
        (is (v/isa? kb call 'tool_invocation CxDesk))
        (is (v/isa? kb call 'event CxDesk))))
    (testing "the second argument of receipt is derived a tool_receipt"
      (is (v/isa? kb Slip 'tool_receipt CxDesk))
      (is (v/isa? kb Slip 'acausal CxDesk)))
    (testing "the first argument of resourceUrl is derived a media_resource"
      (is (v/isa? kb Clip 'media_resource CxDesk))
      (is (v/isa? kb Clip 'information CxDesk)))
    ;; Two rewrites reach a rule concluding either side from a tool.  Unbounded, the node
    ;; engine expands every CxWell rule concluding a spec of `causal`, about 30x per level.
    (testing "no rule of the theory concludes either side of an invocation from its tool"
      (doseq [call [CallOne CallTwo] side '[causal acausal]]
        (is (false? (v/provable? kb (list side call) CxDesk {:max-depth 2})) (str call " " side))))
    (testing "no clash is reported"
      (is (empty? (filter #(some #{CallOne CallTwo Grep Remove Slip Clip}
                                 (flatten (map :sentence (:sides %))))
                          (concat (v/contradictions kb) (v/conflicts kb))))))))

(tu/deftest-kb a-context-that-does-not-see-the-theory-reads-only-its-decontextualized-marks
  (tu/with-terms [CxElsewhere Grep CallOne]
    (v/assert kb (list 'genlCx CxElsewhere 'CxWell) 'CxUniverse)
    (v/assert kb (list 'read_only_software_tool Grep) CxElsewhere)
    (v/assert kb (list 'toolInvoked CallOne Grep) CxElsewhere)
    (doseq [ctx [CxElsewhere 'CxWell 'CxUniverse]]
      (testing (str "no other declaration of a computing relation is read in " ctx)
        ;; The exact-arity classes and `functional` are decontextualized marks, so each
        ;; membership has a copy in CxUniverse, read there and in every context below it.
        (doseq [p binary-relations]
          (is (tu/holds-ask (list 'binary_predicate p) ctx) (str p " in " ctx)))
        (is (tu/holds-ask '(functional toolName) ctx) (str "the functional mark in " ctx))
        (doseq [p ternary-relations]
          (is (tu/holds-ask (list 'ternary_predicate p) ctx) (str p " in " ctx)))
        (doseq [p (concat binary-relations ternary-relations)]
          (is (zero? (declared-positions p ctx)) (str p " in " ctx))
          (is (empty? (v/sentexes-matching kb (list 'comment p '?c) ctx)) (str p " in " ctx)))))
    (testing "the stated fact holds and no argument type is derived from it"
      (is (tu/holds-ask (list 'toolInvoked CallOne Grep) CxElsewhere))
      (is (not (v/isa? kb CallOne 'tool_invocation CxElsewhere))))
    (testing "a wrongly typed argument is not convicted there"
      (is (empty? (problem-types (list 'toolInvoked CallOne 5) CxElsewhere)))
      (is (empty? (problem-types (list 'toolName Grep 5) CxElsewhere))))
    (testing "the kinds are the theory's, so no context that does not see it reads a placement"
      (doseq [ctx [CxElsewhere 'CxWell 'CxUniverse] k kinds]
        (is (not (tu/holds-genl k 'thing ctx)) (str k " in " ctx)))
      (is (not (v/isa? kb Grep 'acausal CxElsewhere))))
    (testing "the default audit, read from CxWell, sweeps none of the kinds"
      (let [swept (into #{} (mapcat (juxt :a :b)) (:pairs-data (v/disjointness-audit kb)))]
        (is (not-any? swept kinds))))))

(tu/deftest-kb check-convicts-a-wrongly-typed-argument-under-the-constraint-only-reading
  ;; the conviction is read under the constraint-only reading: under the default reading an
  ;; argument declaration derives the type it names and convicts no symbol.
  (tu/with-terms [CxDesk Grep CallOne CallTwo Pebble]
    (v/assert kb (list 'genlCx CxDesk 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDesk CPT) 'CxUniverse)
    (v/assert kb (list 'read_only_software_tool Grep) CxDesk)
    (v/assert kb (list 'tool_invocation CallOne) CxDesk)
    (v/assert kb (list 'tool_invocation CallTwo) CxDesk)
    (v/assert kb (list 'stone Pebble) CxDesk)
    (testing "a well-typed sentence draws no problem"
      (is (empty? (problem-types (list 'toolInvoked CallOne Grep) CxDesk)))
      (is (empty? (problem-types (list 'toolName Grep "grep") CxDesk)))
      (is (empty? (problem-types (list 'dnsResolvesTo "example.org" "192.0.2.1") CxDesk)))
      (is (empty? (problem-types (list 'probesPredicate Grep 'parentOf) CxDesk)))
      (is (empty? (problem-types (list 'toolArgType Grep "pattern" 'string) CxDesk))))
    (testing "toolInvoked takes a software tool in position 2"
      (is (= [:arg-type] (problem-types (list 'toolInvoked CallOne Pebble) CxDesk))
          "a stone is tangible and a software tool is intangible")
      (is (= [:arg-type] (problem-types (list 'toolInvoked CallOne 5) CxDesk)))
      (is (= [:arg-type] (problem-types (list 'toolInvoked CallOne "grep") CxDesk))))
    (testing "receipt takes a tool receipt in position 2"
      (is (= [:arg-type] (problem-types (list 'receipt CallOne CallTwo) CxDesk))
          "a tool invocation is disjoint from a tool receipt"))
    (testing "a position declared with quotedArg takes a string"
      (is (= [:quoted-arg-type] (problem-types (list 'toolName Grep 5) CxDesk)))
      (is (= [:quoted-arg-type] (problem-types (list 'dnsResolvesTo "example.org" 5) CxDesk))))
    (testing "probesPredicate takes a predicate in position 2"
      (is (= [:arg-type] (problem-types (list 'probesPredicate Grep "parentOf") CxDesk))))))

(tu/deftest-kb a-tool-has-one-name
  (tu/with-terms [CxDesk Grep]
    (v/assert kb (list 'genlCx CxDesk 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDesk CPT) 'CxUniverse)
    (v/assert kb (list 'read_only_software_tool Grep) CxDesk)
    (v/assert kb (list 'toolName Grep "grep") CxDesk)
    (is (tu/holds-ask (list 'toolName Grep "grep") CxDesk))
    (is (tu/stored-in-clash? kb (list 'toolName Grep "egrep") CxDesk)
        "a second, different name is stored as a member of a functional nogood")))

(tu/deftest-kb a-tool-confers-what-it-enables-on-a-causal-agent-by-default
  (tu/with-terms [CxDesk Viewer Rover Ghost]
    (v/assert kb (list 'genlCx CxDesk 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDesk CPT) 'CxUniverse)
    (v/assert kb (list 'read_only_software_tool Viewer) CxDesk)
    (v/assert kb (list 'toolEnablesCapability Viewer 'image_viewing) CxDesk)
    (v/assert kb (list 'dog Rover) CxDesk)
    (v/assert kb (list 'agentHasTool Rover Viewer) CxDesk)
    (v/assert kb (list 'agentHasTool Ghost Viewer) CxDesk)
    (testing "a causal agent that has the tool can be the doer of the kind"
      (is (tu/holds-ask (list 'hasCapability Rover 'image_viewing) CxDesk)))
    (testing "the rule is guarded, so an agent not known causal is concluded neither capable nor causal"
      (is (not (tu/holds-ask (list 'hasCapability Ghost 'image_viewing) CxDesk)))
      (is (not (v/isa? kb Ghost 'causal CxDesk))))
    (testing "the tool itself is not concluded capable"
      (is (not (tu/holds-ask (list 'hasCapability Viewer 'image_viewing) CxDesk))))
    (testing "a context that does not see the theory concludes nothing"
      (v/assert kb (list 'agentHasTool Rover Viewer) 'CxWell)
      (v/assert kb (list 'toolEnablesCapability Viewer 'image_viewing) 'CxWell)
      (is (not (tu/holds-ask (list 'hasCapability Rover 'image_viewing) 'CxWell))))
    (testing "the conclusion is a default, so a monotonic denial defeats it"
      (v/assert kb (list 'not (list 'hasCapability Rover 'image_viewing)) CxDesk
                {:strength :monotonic})
      (is (not (tu/holds-ask (list 'hasCapability Rover 'image_viewing) CxDesk))))))
