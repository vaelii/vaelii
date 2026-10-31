;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cxtra-social-test
  "The relationship and plural-identity vocabulary of CxTra: nestingPartnerOf,
  chosenSiblingOf, construct and founderOf, and the plurality terms, each narrower than
  a CxSocial relation or type.  CxTra sees CxSocial as well as CxUniverse, and CxWell does not see CxTra,
  so the everyday contexts below CxWell derive none of it, and a user's own context
  opts in by placing itself under CxTra, which carries CxSocial's own relations to it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private SOCX 'CxTra)

(defn- problem-types
  "The `:type` of each problem `check` reports for `sentence` in `ctx`, or of the argument
  conviction `assert` holds it inert under, under the constraint-only reading."
  [sentence ctx]
  (tu/without-entailing
   (or (not-empty (mapv :type (v/check tu/*kb* sentence ctx)))
       (into [] (keep :type) [(tu/write-conviction tu/*kb* sentence ctx)]))))

(tu/deftest-kb cxtra-is-opt-in-and-sees-cxsocial
  (testing "the theory sees CxSocial, and through it CxUniverse"
    (is (tu/holds-sees SOCX 'CxSocial))
    (is (tu/holds-sees SOCX 'CxUniverse)))
  (testing "neither CxWell, CxSocial, nor the upper ontology sees the theory"
    (is (not (tu/holds-sees 'CxWell SOCX)))
    (is (not (tu/holds-sees 'CxSocial SOCX)))
    (is (not (tu/holds-sees 'CxUniverse SOCX)))))

(tu/deftest-kb cxwell-concludes-none-of-the-extension
  (tu/with-terms [P1 P2 Unit]
    (v/assert kb (list 'human P1) 'CxWell)
    (v/assert kb (list 'human P2) 'CxWell)
    (v/assert kb (list 'romanticPartnerOf P1 P2) 'CxWell)
    (v/assert kb (list 'dwellsIn P1 Unit) 'CxWell)
    (v/assert kb (list 'dwellsIn P2 Unit) 'CxWell)
    (testing "CxSocial's own vocabulary still derives in CxWell"
      (is (tu/holds-ask (list 'roommateOf P1 P2) 'CxWell)))
    (testing "the extension's nestingPartnerOf does not, though both antecedents hold"
      (is (not (tu/holds-ask (list 'nestingPartnerOf P1 P2) 'CxWell))))))

(tu/deftest-kb a-user-context-under-the-extension-derives-nestingpartnerof
  (tu/with-terms [CxHome P1 P2 Unit]
    (v/assert kb (list 'genlCx CxHome 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human P1) CxHome)
    (v/assert kb (list 'human P2) CxHome)
    (v/assert kb (list 'romanticPartnerOf P1 P2) CxHome)
    (testing "romantic partners who are not yet roommates are not yet nesting partners (red)"
      (is (not (tu/holds-ask (list 'nestingPartnerOf P1 P2) CxHome))))
    (v/assert kb (list 'dwellsIn P1 Unit) CxHome)
    (v/assert kb (list 'dwellsIn P2 Unit) CxHome)
    (testing "co-dwelling derives roommateOf, which with romanticPartnerOf derives nestingPartnerOf (green)"
      (is (tu/holds-ask (list 'roommateOf P1 P2) CxHome))
      (is (tu/holds-ask (list 'nestingPartnerOf P1 P2) CxHome)))
    (testing "a context that does not see the extension still concludes none of it"
      (doseq [ctx ['CxWell 'CxSocial 'CxUniverse]]
        (is (not (tu/holds-ask (list 'nestingPartnerOf P1 P2) ctx)) (str "nestingPartnerOf in " ctx))))))

(tu/deftest-kb each-relation-specializes-what-it-is-a-kind-of
  (doseq [[sub super] '[[chosenSiblingOf relativeOf]
                        [nestingPartnerOf romanticPartnerOf]
                        [nestingPartnerOf roommateOf]
                        [founderOf originatorOf]]]
    (is (tu/holds-genl sub super SOCX))
    (is (not (tu/holds-genl sub super 'CxSocial))))
  (is (not (tu/holds-genl 'chosenSiblingOf 'siblingOf SOCX)))
  (is (not (tu/holds-genl 'siblingOf 'chosenSiblingOf SOCX))))

(tu/deftest-kb a-user-context-under-the-extension-concludes-from-each-relation
  (tu/with-terms [CxHome P1 P2 P3 P4]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (doseq [p [P1 P2 P3 P4]] (v/assert kb (list 'human p) CxHome))
    (v/assert kb (list 'chosenSiblingOf P1 P2) CxHome)
    (v/assert kb (list 'nestingPartnerOf P3 P4) CxHome)
    (is (tu/holds-ask (list 'relativeOf P1 P2) CxHome))
    (is (tu/holds-ask (list 'knows P1 P2) CxHome))
    (is (not (tu/holds-ask (list 'siblingOf P1 P2) CxHome)))
    (is (tu/holds-ask (list 'romanticPartnerOf P3 P4) CxHome))
    (is (tu/holds-ask (list 'roommateOf P3 P4) CxHome))))

(tu/deftest-kb the-plurality-terms-partition-person
  (doseq [k '[singlet plural_system alter]]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment k '?c) SOCX))) (str k))
    (is (tu/holds-genl k 'person SOCX) (str k))
    (is (not (tu/holds-genl k 'person 'CxSocial)) (str k)))
  (testing "the declaration is a partition, not a bare separation"
    (is (= 1 (count (v/sentexes-matching kb '(partition person singlet plural_system alter) SOCX))))
    (is (empty? (v/sentexes-matching kb '(separating person singlet plural_system alter) SOCX))))
  (testing "disjoint: no person is two of the three"
    (is (v/disjoint? kb 'singlet 'plural_system SOCX))
    (is (v/disjoint? kb 'alter 'singlet SOCX))
    (is (v/disjoint? kb 'alter 'plural_system SOCX))))

(tu/deftest-kb the-plurality-terms-are-time-varying
  ;; This branch states rigidity in the type's comment (handbook ch. 12): the comment says
  ;; whether a member can stop being one and go on existing, with the case that shows it.
  (doseq [k '[singlet plural_system alter]]
    (let [cs (map (comp last :sentence) (v/sentexes-matching kb (list 'comment k '?c) SOCX))]
      (is (= 1 (count cs)) (str k " carries one comment"))
      (is (every? #(re-find #"[Tt]ime-varying" (str %)) cs) (str k " is stated time-varying"))
      (is (every? #(re-find #"can stop being one and go on existing" (str %)) cs)
          (str k " states the case")))))

(tu/deftest-kb every-person-is-one-of-the-three
  (tu/with-terms [CxHome Pat Quinn]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human Pat) CxHome)
    (v/assert kb (list 'human Quinn) CxHome)
    (testing "a person with nothing known is assigned no part"
      (doseq [k '[singlet plural_system alter]]
        (is (not (tu/holds-ask (list k Quinn) CxHome)) (str k))))
    (v/assert kb (list 'not (list 'singlet Pat)) CxHome)
    (v/assert kb (list 'not (list 'alter Pat)) CxHome)
    (testing "a person who is neither a singlet nor an alter is a plural system"
      (is (tu/holds-ask (list 'plural_system Pat) CxHome))
      (is (not (tu/holds-ask (list 'plural_system Pat) 'CxSocial))
          "a context that does not see the partition does not conclude it"))
    (testing "a person denied all three contradicts the partition"
      (v/assert kb (list 'not (list 'singlet Quinn)) CxHome)
      (v/assert kb (list 'not (list 'alter Quinn)) CxHome)
      (is (tu/stored-in-clash? kb (list 'not (list 'plural_system Quinn)) CxHome)))))

(tu/deftest-kb two-alters-of-one-system-are-headmates-and-need-not-know-each-other
  (tu/with-terms [CxHome Sys A1 A2 Other]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'plural_system Sys) CxHome)
    (doseq [a [A1 A2 Other]] (v/assert kb (list 'alter a) CxHome))
    (v/assert kb (list 'alterOf A1 Sys) CxHome)
    (v/assert kb (list 'alterOf A2 Sys) CxHome)
    (is (tu/holds-ask (list 'headmateOf A1 A2) CxHome))
    (is (tu/holds-ask (list 'headmateOf A2 A1) CxHome))
    (is (not (tu/holds-ask (list 'headmateOf A1 A1) CxHome)) "an alter is not its own headmate")
    (is (not (tu/holds-ask (list 'headmateOf A1 Other) CxHome)))
    (testing "headmates are not concluded to know each other"
      (is (not (tu/holds-ask (list 'knows A1 A2) CxHome))))
    (testing "a context that does not see the extension concludes none of it"
      (is (not (tu/holds-ask (list 'headmateOf A1 A2) 'CxSocial))))))

(defn- known-alters
  "The alters `ctx` knows of `system`: the fillers of (alterOf ?a system) it believes."
  [kb system ctx]
  (into #{} (map '?a) (v/query kb (list 'alterOf '?a system) ctx)))

(defn- under-counted
  "The systems among `systems` with fewer than two known alters."
  [kb systems ctx]
  (into #{} (filter #(< (count (known-alters kb % ctx)) 2)) systems))

(tu/deftest-kb a-plural-system-has-at-least-two-known-alters
  ;; A plural system has two or more alters, but the KB may know fewer of them than exist,
  ;; so the vocabulary states no count rule and no audit: a system with one known alter is
  ;; no conflict.  The count is checked here, over this fixture, where every alter is known.
  (tu/with-terms [CxHome SysA SysB Lone A1 A2 B1 B2 B3 L1]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (doseq [sys [SysA SysB Lone]] (v/assert kb (list 'plural_system sys) CxHome))
    (doseq [[a sys] [[A1 SysA] [A2 SysA] [B1 SysB] [B2 SysB] [B3 SysB] [L1 Lone]]]
      (v/assert kb (list 'alter a) CxHome)
      (v/assert kb (list 'alterOf a sys) CxHome))
    (testing "each fully described system has at least two known alters"
      (is (= #{A1 A2} (known-alters kb SysA CxHome)))
      (is (= #{B1 B2 B3} (known-alters kb SysB CxHome)))
      (is (empty? (under-counted kb [SysA SysB] CxHome))))
    (testing "the check flags a system with fewer than two known alters"
      (is (= #{Lone} (under-counted kb [SysA SysB Lone] CxHome))))
    (testing "and the KB does not: a system with one known alter is believed, not a clash"
      (is (tu/holds-ask (list 'plural_system Lone) CxHome))
      (is (tu/holds-ask (list 'alterOf L1 Lone) CxHome)))))

(tu/deftest-kb a-construct-is-a-person-uncommitted-on-tangibility-and-no-organism
  (is (= 1 (count (v/sentexes-matching kb '(comment construct ?c) SOCX))))
  (is (tu/holds-genl 'construct 'person SOCX))
  (is (not (tu/holds-genl 'construct 'made SOCX)) "being built does not make a construct tangible")
  (is (not (tu/holds-genl 'construct 'tangible SOCX)))
  (is (not (tu/holds-genl 'construct 'intangible SOCX)))
  (is (v/disjoint? kb 'construct 'organism SOCX))
  (is (v/disjoint? kb 'construct 'human SOCX))
  (is (v/disjoint? kb 'construct 'computer SOCX) "a construct runs on a computer and is not one")
  (is (v/disjoint? kb 'construct 'computational_system SOCX) "a construct is never its own process")
  (is (v/disjoint? kb 'construct 'organization SOCX) "a construct is one person, not a body of them")
  (is (not (tu/holds-genl 'construct 'person 'CxWell))))

(tu/deftest-kb a-construct-runs-in-a-seat-on-a-computer-and-is-neither
  (tu/with-terms [CxHome Mind Pod Spare Box]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'construct Mind) CxHome)
    (v/assert kb (list 'seat Pod) CxHome)
    (v/assert kb (list 'seat Spare) CxHome)
    (v/assert kb (list 'computer Box) CxHome)
    (v/assert kb (list 'hasSeat Mind Pod) CxHome)
    (v/assert kb (list 'hasSeat Mind Spare) CxHome)
    (v/assert kb (list 'runsOn Pod Box) CxHome)
    (is (tu/holds-ask (list 'hasSeat Mind Pod) CxHome))
    (is (tu/holds-ask (list 'hasSeat Mind Spare) CxHome) "a construct can run in two seats")
    (is (not (tu/holds-ask (list 'equals Pod Spare) CxHome)))
    (is (tu/holds-genl 'seat 'computational_system SOCX))
    (is (v/disjoint? kb 'construct 'seat SOCX) "a construct is never its own seat")
    (is (not (tu/holds-ask (list 'runsOn Mind Box) CxHome)) "runsOn is the seat's, not the construct's")))

(tu/deftest-kb a-founder-founds-a-construct-and-is-its-originator
  (tu/with-terms [CxHome Maker Made Firm]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human Maker) CxHome)
    (v/assert kb (list 'construct Made) CxHome)
    (v/assert kb (list 'organization Firm) CxHome)
    (testing "a construct in position 2 is accepted"
      (is (empty? (problem-types (list 'founderOf Maker Made) CxHome))))
    (testing "an organization in position 2 is refused"
      (is (= [:arg-type] (problem-types (list 'founderOf Maker Firm) CxHome))))
    (v/assert kb (list 'founderOf Maker Made) CxHome)
    (is (tu/holds-ask (list 'originatorOf Maker Made) CxHome))
    (is (tu/holds-ask (list 'relativeOf Maker Made) CxHome))))
