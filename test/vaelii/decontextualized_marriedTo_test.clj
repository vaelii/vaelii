(ns vaelii.decontextualized-marriedTo-test
  "Demonstrates that decontextualizing marriedTo causes temporal leakage:
   a person married in one decade becomes provably married in all decades.
   Halle Berry married David Justice (1993), Eric Benet (2001), and
   Olivier Martinez (2013). With decontextualization, all three marriages
   are provable from any temporal context. Without it, each marriage stays
   in its own decade.

   Test data after Ken Murray's canonical Muffet: Halle Berry is
   the canonical multiply-married person."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each tu/neutral)

(defn setup-temporal-marriages
  "Three temporal contexts, each seeing SocialContext (so the marriedTo->knows
   rule is visible), each with one marriage."
  [kb]
  (v/assert kb '(genlContext NinetiesContext SocialContext) 'UniverseContext)
  (v/assert kb '(genlContext OughtiesContext SocialContext) 'UniverseContext)
  (v/assert kb '(genlContext TeensContext SocialContext) 'UniverseContext)
  (v/assert kb '(marriedTo HalleBerry DavidJustice) 'NinetiesContext)
  (v/assert kb '(marriedTo HalleBerry EricBenet) 'OughtiesContext)
  (v/assert kb '(marriedTo HalleBerry OlivierMartinez) 'TeensContext))

(tu/deftest-kb decontextualized-marriedTo-leaks-across-temporal-contexts
  (testing "with default starter (marriedTo decontextualized), all three
            marriages are provable from any single decade — temporal leakage"
    (setup-temporal-marriages kb)
    (is (v/provable? kb '(marriedTo HalleBerry DavidJustice) 'NinetiesContext))
    (is (v/provable? kb '(marriedTo HalleBerry EricBenet) 'NinetiesContext)
        "BUG: Benet marriage (2001) is provable in the 1990s")
    (is (v/provable? kb '(marriedTo HalleBerry OlivierMartinez) 'NinetiesContext)
        "BUG: Martinez marriage (2013) is provable in the 1990s")))

(tu/deftest-kb decontextualized-marriedTo-leaks-into-derived-knows
  (testing "the temporal leakage cascades through the marriedTo->knows rule"
    (setup-temporal-marriages kb)
    (is (v/provable? kb '(knows HalleBerry DavidJustice) 'NinetiesContext))
    (is (v/provable? kb '(knows HalleBerry EricBenet) 'NinetiesContext)
        "BUG: knows Benet in the 1990s via leaked marriedTo")
    (is (v/provable? kb '(knows HalleBerry OlivierMartinez) 'NinetiesContext)
        "BUG: knows Martinez in the 1990s via leaked marriedTo")))

(tu/deftest-kb contextualized-marriedTo-confines-to-own-decade
  (testing "after retracting decontextualizedPredicate, each marriage stays
            in its own temporal context"
    (when-let [h (v/handle-of kb '(decontextualizedPredicate marriedTo) 'SocietyContext)]
      (v/retract! kb h))
    (setup-temporal-marriages kb)
    (testing "marriedTo from NinetiesContext: only Justice"
      (is (v/provable? kb '(marriedTo HalleBerry DavidJustice) 'NinetiesContext))
      (is (not (v/provable? kb '(marriedTo HalleBerry EricBenet) 'NinetiesContext)))
      (is (not (v/provable? kb '(marriedTo HalleBerry OlivierMartinez) 'NinetiesContext))))
    (testing "knows from NinetiesContext: only Justice"
      (is (v/provable? kb '(knows HalleBerry DavidJustice) 'NinetiesContext))
      (is (not (v/provable? kb '(knows HalleBerry EricBenet) 'NinetiesContext)))
      (is (not (v/provable? kb '(knows HalleBerry OlivierMartinez) 'NinetiesContext))))
    (testing "marriedTo from OughtiesContext: only Benet"
      (is (not (v/provable? kb '(marriedTo HalleBerry DavidJustice) 'OughtiesContext)))
      (is (v/provable? kb '(marriedTo HalleBerry EricBenet) 'OughtiesContext))
      (is (not (v/provable? kb '(marriedTo HalleBerry OlivierMartinez) 'OughtiesContext))))
    (testing "knows from OughtiesContext: only Benet"
      (is (not (v/provable? kb '(knows HalleBerry DavidJustice) 'OughtiesContext)))
      (is (v/provable? kb '(knows HalleBerry EricBenet) 'OughtiesContext))
      (is (not (v/provable? kb '(knows HalleBerry OlivierMartinez) 'OughtiesContext))))))
