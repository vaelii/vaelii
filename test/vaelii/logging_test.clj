;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.logging-test
  "The log dial (`vaelii.core/set-log-level`, `vaelii.impl.logging`): a level a running
  process can turn, checked by **capturing what is printed** rather than by eye.

  Trove's console backend prints to `*out*`, so a capture is `with-out-str` around a
  provoked `log!` — which runs the real installed backend rather than a stand-in for
  it.  Three properties are worth the test and all three are here: the level decides
  what arrives, an illegal level is refused *without* moving the dial (a bad argument
  that left the process silent would be the failure mode with teeth), and opening a KB
  installs nothing at all — the library-shape invariant a later convenience is most
  likely to break.

  Every test restores the root of `taoensso.trove/*log-fn*` and the dial, since both are
  process-wide and the suite's own quiet floor is one of them."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.config :as config]
            [vaelii.impl.logging :as logging]
            [vaelii.test-util :as tu]))

(defn- restore-logging
  "An `:each` fixture: put the root `*log-fn*` and the dial back after every test.  The
  suite runs at `:error` because the `:test` profile turned this same dial, so a test
  that left it at `:debug` would make every namespace after it loud."
  [f]
  (let [root  (.getRawRoot #'trove/*log-fn*)
        level (logging/current-level)]
    (try (f)
         (finally
           (reset! @#'logging/dial level)
           (alter-var-root #'trove/*log-fn* (constantly root))))))

(use-fixtures :each restore-logging)

(defn- emitted
  "What the engine prints at `level` when a `:debug`, a `:warn` and an `:error` are
  provoked — the three levels one test needs, captured off `*out*`."
  [level]
  (v/set-log-level level)
  (with-out-str
    (trove/log! {:level :debug :id ::probe :msg "a debug line"})
    (trove/log! {:level :warn  :id ::probe :msg "a warn line"})
    (trove/log! {:level :error :id ::probe :msg "an error line"})))

(deftest the-level-decides-what-is-emitted
  (testing ":debug prints all three"
    (let [out (emitted :debug)]
      (is (re-find #"a debug line" out))
      (is (re-find #"a warn line" out))
      (is (re-find #"an error line" out))))
  (testing ":warn drops the debug and keeps the rest"
    (let [out (emitted :warn)]
      (is (not (re-find #"a debug line" out)))
      (is (re-find #"a warn line" out))
      (is (re-find #"an error line" out))))
  (testing ":error keeps only the error"
    (let [out (emitted :error)]
      (is (not (re-find #"a debug line" out)))
      (is (not (re-find #"a warn line" out)))
      (is (re-find #"an error line" out))))
  (testing "and the dial moves both ways, on a process that is already running"
    (is (= :trace (v/set-log-level :trace)))
    (is (= :trace (v/log-level)))
    (is (re-find #"a warn line" (emitted :trace)))))

(deftest a-level-above-the-dial-that-trove-ranks-higher-than-error-still-prints
  ;; The dial takes five levels; Trove ranks seven.  A `:fatal` or `:report` message
  ;; sorts above `:error`, so the quietest setting is still not silence — a level the
  ;; ranking did not know would sort at zero and vanish under every setting.
  (v/set-log-level :error)
  (let [out (with-out-str
              (trove/log! {:level :fatal  :id ::probe :msg "a fatal line"})
              (trove/log! {:level :report :id ::probe :msg "a report line"}))]
    (is (re-find #"a fatal line" out))
    (is (re-find #"a report line" out))))

(deftest an-illegal-level-is-refused-and-the-dial-does-not-move
  (v/set-log-level :warn)
  (doseq [bad [:verbose "debug" :DEBUG nil :off]]
    (testing (str "set-log-level " (pr-str bad))
      (let [e (is (thrown? clojure.lang.ExceptionInfo (v/set-log-level bad)))
            d (ex-data e)]
        (is (= :unknown-option (:type d)) "the roster's own type, not a new one")
        (is (= [:error :warn :info :debug :trace] (:known d)))
        (is (re-find #"want one of" (ex-message e))
            "and the message names the five, since a refusal an operator cannot act on
             is a refusal they retry"))))
  (testing "the level in force is the one set before the bad argument, not silence"
    (is (= :warn (v/log-level)))
    (is (re-find #"a warn line" (emitted :warn)))))

(deftest opening-a-kb-installs-no-backend
  ;; The library-shape invariant: a host application that installed its own `*log-fn*`
  ;; must not have it replaced by a KB it opened.  Setting a level unasked is how a
  ;; library takes over its host's logging, so the environment variable and the explicit
  ;; call install a backend and nothing else does.
  (let [collected (atom [])
        collector (fn [_ns _coords level _id _payload] (swap! collected conj level))]
    (alter-var-root #'trove/*log-fn* (constantly collector))
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog Muffet]
        (v/assert kb (list dog Muffet) 'UniverseContext))
      (is (identical? collector (.getRawRoot #'trove/*log-fn*))
          "open-kb, assert, chain and settle left the host's backend in place")
      (is (some? kb)))))

(def ^:private probe-property
  "A property name standing in for `VAELII_LOG_LEVEL`: a JVM cannot set its own
  environment, and the domain is what the accessor adds to `prop-enum`."
  "vaelii.test.log-level")

(defn- read-probe [value]
  (System/setProperty probe-property value)
  (try (config/prop-enum probe-property config/log-level-spellings nil
                         "error, warn, info, debug or trace")
       (finally (System/clearProperty probe-property))))

(deftest the-environment-and-the-function-take-the-same-five-levels
  (is (= (set logging/dial-levels) (set (vals config/log-level-spellings)))
      "two rosters for one dial is one of them wrong")
  (is (= ["debug" "error" "info" "trace" "warn"] (sort (keys config/log-level-spellings)))
      "and the spellings are the level names themselves")
  (testing "each spelling reads as its level, case-insensitively"
    (doseq [[spelling level] config/log-level-spellings]
      (is (= level (read-probe spelling)) spelling)
      (is (= level (read-probe (.toUpperCase ^String spelling))) spelling)))
  (testing "a value outside them is refused rather than read as the nearest legal one"
    (doseq [bad ["verbose" "quiet" "all" "0"]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo (read-probe bad)) bad)]
        (is (= :unknown-option (:type (ex-data e))))
        (is (re-find #"error, warn, info, debug or trace" (ex-message e))
            "and the message names the five")))))

;; ---- what a `:debug` run has to show for itself -------------------------
;;
;; The dial is worth turning only if something is behind it.  Three statements sit at
;; run boundaries and each answers a question one of the `:warn` sites raises without
;; answering: what a chaining run did (`chain/chain-all`), what a settle cost
;; (`settle`), and which rule a dropped conclusion came from — the ledger files a rule
;; *handle*, which is not a thing an operator reading a log can look up.

(deftest a-debug-run-says-what-each-run-did
  (v/set-log-level :debug)
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog barks Muffet]
      (let [out (with-out-str
                  (v/assert-rule kb [(list dog '?x)] (list barks '?x) 'UniverseContext)
                  (v/assert kb (list dog Muffet) 'UniverseContext))]
        (is (re-find #"::chain-run" out) "a chaining run reports, truncated or not")
        (is (re-find #":derived 1" out) "with what it concluded")
        (is (re-find #"::settled" out) "and a settle reports what it cost")
        (is (re-find #":passes 1" out)))
      ;; the floor again, so the fixture's retraction settles quietly: that settle is
      ;; nobody's subject here, and its lines land in the suite's own output
      (v/set-log-level :error))))

(deftest a-dropped-conclusion-at-debug-names-the-rule-behind-the-handle
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog barksAt Muffet IslandAContext IslandBContext]
      ;; rule and fact in island contexts with no common descendant: the join
      ;; completes and the conclusion has nowhere to land
      (v/assert-rule kb [(list dog '?x)] (list barksAt '?x '?x) IslandAContext)
      (v/set-log-level :debug)
      (let [out (with-out-str (v/assert kb (list dog Muffet) IslandBContext))]
        (is (re-find #"::dropped-conclusion" out) "the drop itself is a :warn")
        (is (re-find #"::dropping-rule" out)
            "and at :debug the rule the handle stands for follows it")
        (is (re-find (re-pattern (str "implies.*" dog)) out)
            "as the sentence its author wrote"))
      (v/set-log-level :error)))
  (testing "at :warn the drop is reported and the rule lookup is not made"
    (v/set-log-level :warn)
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog barksAt Muffet IslandAContext IslandBContext]
        (v/assert-rule kb [(list dog '?x)] (list barksAt '?x '?x) IslandAContext)
        (let [out (with-out-str (v/assert kb (list dog Muffet) IslandBContext))]
          (is (re-find #"::dropped-conclusion" out))
          (is (not (re-find #"::dropping-rule" out))))))))

(deftest the-suite-is-quieted-through-this-dial-and-not-a-copy-of-it
  ;; `project.clj`'s `:test` injections call `logging/set-level`.  Two mechanisms
  ;; spelled the same way would let the suite stay quiet on the day the public one
  ;; stopped working, so the dial's current reading is the assertion that they are one.
  (is (= (keyword (or (System/getenv "VAELII_TEST_LOG_LEVEL") "error"))
         (logging/current-level))
      "the suite's floor is the dial, set by the injection"))
