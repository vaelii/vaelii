;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.eager-reify-test
  "`eagerly_reifiable_function`: core.txt's general rule reifies every application of an
  eagerly reifiable function whose arguments meet its argument constraints. The
  constraint check is a TEMPORARY rule over a unary function's one position, read one arg
  declaration at a time and without argGenl. The `^:red` tests state the general reading."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:private U 'CxUniverse)

(defn- load-eager-fixture! [kb]
  (tu/load-starter! kb)
  (doseq [sentence '[(unary_predicate test_gadget)
                     (unary_predicate test_shiny_gadget)
                     (unary_predicate test_small_gadget)
                     (genl test_small_gadget test_gadget)
                     (test_gadget TestWidget)
                     (test_gadget TestSprocket)
                     (test_shiny_gadget TestSprocket)
                     (unary_function TestReadingFn)
                     (reifiable_function TestReadingFn)
                     (arg TestReadingFn 1 test_gadget)
                     (eagerly_reifiable_function TestReadingFn)
                     (unary_function TestShinyReadingFn)
                     (reifiable_function TestShinyReadingFn)
                     (arg TestShinyReadingFn 1 test_gadget)
                     (arg TestShinyReadingFn 1 test_shiny_gadget)
                     (eagerly_reifiable_function TestShinyReadingFn)
                     (binary_function TestPairReadingFn)
                     (reifiable_function TestPairReadingFn)
                     (arg TestPairReadingFn 1 test_gadget)
                     (arg TestPairReadingFn 2 test_shiny_gadget)
                     (eagerly_reifiable_function TestPairReadingFn)
                     (unary_function TestKindReadingFn)
                     (reifiable_function TestKindReadingFn)
                     (argGenl TestKindReadingFn 1 test_gadget)
                     (eagerly_reifiable_function TestKindReadingFn)]]
    (v/assert kb sentence U {:strength :monotonic}))
  kb)

(use-fixtures :once (tu/loaded load-eager-fixture!))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb an-argument-meeting-the-constraint-has-its-application-reified
  (is (true? (v/ask? kb '(reify (TestReadingFn TestWidget)) U)))
  (is (true? (v/ask? kb '(comment (TestReadingFn TestWidget)
                                  "@hack: temporary implementation of `reify` until it has engine support")
                     U)))
  (is (not (v/ask? kb '(reify (TestReadingFn TestReadingFn)) U)))
  (is (empty? (v/contradictions kb))))

(tu/deftest-kb ^:red an-argument-meeting-one-of-two-constraints-is-not-reified
  ;; The TEMPORARY rule reads each arg declaration alone, so TestWidget passes.
  (is (true? (v/ask? kb '(reify (TestShinyReadingFn TestSprocket)) U)))
  (is (not (v/ask? kb '(reify (TestShinyReadingFn TestWidget)) U))))

(tu/deftest-kb ^:red a-binary-function-has-its-applications-reified
  ;; The TEMPORARY rule reads a unary function's one position only.
  (is (true? (v/ask? kb '(reify (TestPairReadingFn TestWidget TestSprocket)) U)))
  (is (not (v/ask? kb '(reify (TestPairReadingFn TestSprocket TestWidget)) U))))

(tu/deftest-kb ^:red an-argument-meeting-an-arg-genl-constraint-is-reified
  ;; The TEMPORARY rule ignores argGenl.
  (is (true? (v/ask? kb '(reify (TestKindReadingFn test_small_gadget)) U))))
