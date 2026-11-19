;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.perception-test
  "The perception vocabulary of CxTra: the perception relations, shipped in the opt-in
  theory CxTra below CxUniverse. CxWell does not see the theory, so the everyday contexts
  below CxWell take in no perception relation, and a user's own context opts in by
  placing itself under CxTra.

  `sees` specializes `perceives` through a `genl` edge stated inside the theory, and
  `seeImage` and `watchVideo` conclude `sees` by a rule guarded by `sees`'s `spatial`
  second argument. A context under CxTra reads the whole chain for a spatial
  image or video; a context that does not see the theory reads only the fact asserted
  there."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private PCP 'CxTra)

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(tu/deftest-kb the-theory-is-opt-in-below-cxuniverse
  (testing "the theory sees the upper ontology through CxUniverse"
    (is (tu/holds-sees PCP 'CxUniverse)))
  (testing "neither CxWell nor the upper ontology sees the theory"
    (is (not (tu/holds-sees 'CxWell PCP)))
    (is (not (tu/holds-sees 'CxUniverse PCP)))))

(tu/deftest-kb the-specialization-chain-is-the-theorys-own
  (is (tu/holds-genl 'sees 'perceives PCP))
  (is (not (tu/holds-genl 'sees 'perceives 'CxUniverse)))
  (doseq [sub '[seeImage watchVideo]]
    (is (not (tu/holds-genl sub 'sees PCP)) (str sub " reaches sees by a rule, not a genl edge"))))

(tu/deftest-kb an-aspatial-image-seen-stores-no-clash
  ;; A genl edge to `sees` would carry `(arg sees 2 spatial)` down and mint `(spatial Img)`,
  ;; which the `spatial`/`aspatial` partition convicts.
  (tu/with-terms [CxRoom Ann Img Clip]
    (v/assert kb (list 'genlCx CxRoom PCP) 'CxUniverse)
    (v/assert kb (list 'aspatial Img) CxRoom)
    (v/assert kb (list 'aspatial Clip) CxRoom)
    (is (not (tu/stored-in-clash? kb (list 'seeImage Ann Img) CxRoom)))
    (is (not (tu/stored-in-clash? kb (list 'watchVideo Ann Clip) CxRoom)))
    (is (not (tu/holds-ask (list 'spatial Img) CxRoom)))
    (is (not (tu/holds-ask (list 'sees Ann Img) CxRoom)))))

(tu/deftest-kb cxwell-concludes-no-specialization
  ;; CxWell does not see CxTra: a fact asserted at the narrowest predicate is
  ;; itself visible there (an assert is never refused), but it specializes nothing.
  (tu/with-terms [Viewer Image Watcher Video]
    (v/assert kb (list 'seeImage Viewer Image) 'CxWell)
    (v/assert kb (list 'watchVideo Watcher Video) 'CxWell)
    (testing "the asserted fact holds"
      (is (tu/holds-ask (list 'seeImage Viewer Image) 'CxWell))
      (is (tu/holds-ask (list 'watchVideo Watcher Video) 'CxWell)))
    (testing "no specialization above it holds"
      (is (not (tu/holds-ask (list 'sees Viewer Image) 'CxWell)))
      (is (not (tu/holds-ask (list 'perceives Viewer Image) 'CxWell)))
      (is (not (tu/holds-ask (list 'sees Watcher Video) 'CxWell))))))

(tu/deftest-kb a-user-context-under-cxtra-derives-the-chain
  (tu/with-terms [CxRoom Viewer Image Watcher Video Seer Scene]
    (v/assert kb (list 'genlCx CxRoom 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom PCP) 'CxUniverse)
    (v/assert kb (list 'spatial Image) CxRoom)
    (v/assert kb (list 'spatial Video) CxRoom)
    (v/assert kb (list 'seeImage Viewer Image) CxRoom)
    (v/assert kb (list 'watchVideo Watcher Video) CxRoom)
    (v/assert kb (list 'sees Seer Scene) CxRoom)
    (testing "seeImage of a spatial image derives sees and perceives"
      (is (tu/holds-ask (list 'sees Viewer Image) CxRoom))
      (is (tu/holds-ask (list 'perceives Viewer Image) CxRoom)))
    (testing "watchVideo of a spatial video derives sees and perceives"
      (is (tu/holds-ask (list 'sees Watcher Video) CxRoom))
      (is (tu/holds-ask (list 'perceives Watcher Video) CxRoom)))
    (testing "sees derives perceives, and derives from neither spec"
      (is (tu/holds-ask (list 'perceives Seer Scene) CxRoom))
      (is (not (tu/holds-ask (list 'seeImage Seer Scene) CxRoom)))
      (is (not (tu/holds-ask (list 'watchVideo Seer Scene) CxRoom))))
    (testing "a context that does not see the theory still concludes none of it"
      (doseq [ctx ['CxWell 'CxUniverse]]
        (is (not (tu/holds-ask (list 'sees Viewer Image) ctx)) (str "Viewer sees in " ctx))
        (is (not (tu/holds-ask (list 'perceives Seer Scene) ctx)) (str "Seer perceives in " ctx))))))

(tu/deftest-kb image-viewing-is-an-acausal-event-kind-the-theory-states
  (testing "the edge is the theory's, not the upper ontology's"
    (is (tu/holds-genl 'image_viewing 'acausal_event PCP))
    (is (tu/holds-genl 'image_viewing 'event PCP))
    (is (tu/holds-genl 'image_viewing 'acausal PCP))
    (is (not (tu/holds-genl 'image_viewing 'acausal_event 'CxUniverse)))))

(tu/deftest-kb a-user-context-under-cxtra-derives-able-of-image-viewing
  (tu/with-terms [CxRoom Viewer]
    (v/assert kb (list 'genlCx CxRoom 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom PCP) 'CxUniverse)
    (v/assert kb (list 'able Viewer 'image_viewing) CxRoom)
    (testing "a context under the theory reads the ability and its causal class"
      (is (tu/holds-ask (list 'able Viewer 'image_viewing) CxRoom))
      (is (tu/holds-ask (list 'able Viewer 'event) CxRoom))
      (is (tu/holds-ask (list 'able Viewer 'acausal_event) CxRoom)))
    (testing "a context that does not see the theory concludes no such ability class"
      (doseq [ctx ['CxWell 'CxUniverse]]
        (is (not (tu/holds-ask (list 'able Viewer 'acausal_event) ctx))
            (str "Viewer able acausal_event in " ctx))))))
