;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-programs-test
  "The sample programs under test/programs/asp.  Each is a run file stating an ASP program
  in vaelii, beside its twin `<name>.lp` in clingo's language.  Each test runs one program
  over the core base and checks every read's answer count and optimum cost vector.  Where
  the clingo executable answers on the PATH, it also solves the twin under the read's
  `#solve` options and checks every read against the twin's answer."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [is use-fixtures]]
            [vaelii.host.run :as run]
            [vaelii.impl.asp.clasp :as clasp]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.config :as config]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu :refer [deftest-kb]]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private asp? (solver/available?))

(def ^:private clingo? (binding [clasp/*clasp-binary* "clingo"] (clasp/available?)))

(def ^:private dir (io/file "test" "programs" "asp"))

(defn- twin-text
  "The text of `<name>.lp`, each `#include \"f\".` line replaced by the text of `f`: the
  twin reaches clingo on stdin, where an include has no directory to resolve against."
  [name]
  (str/replace (slurp (io/file dir (str name ".lp"))) #"(?m)^#include \"([^\"]+)\"\.$"
               (fn [[_ f]] (slurp (io/file dir f)))))

(defn- clingo-names
  "Each symbol of `program`'s entries and reads, keyed by its clingo spelling: the first
  character lowered."
  [{:keys [entries reads]}]
  (into {}
        (comp (mapcat #(tree-seq seq? seq %))
              (filter symbol?)
              (map (fn [s] [(str (str/lower-case (subs (name s) 0 1)) (subs (name s) 1)) s])))
        (concat (map first entries) (map :arg reads))))

(defn- sentence-of
  "clingo's atom `s`, such as `queenAt(1,2)`, as a sentence, each name read back through
  `names`."
  [names s]
  (let [[_ f args] (re-matches #"([a-z_][A-Za-z0-9_']*)(?:\((.*)\))?" s)]
    (apply list (names f (symbol f))
           (for [a (some-> args (str/split #","))]
             (or (parse-long a) (names a (symbol a)))))))

(defn- instances [pattern atoms] (set (filter #(res/unify pattern % {}) atoms)))

(defn- own-answer
  "`read`'s answer as `twin-answer` gives the twin's."
  [{:keys [directive answer-sets answer-set-costs answers status costs]}]
  (merge {:status status :costs costs}
         (case directive
           models           {:answer-sets (frequencies (map #(vector (set %1) %2) answer-sets answer-set-costs))}
           model            {:optimal? true}
           (brave cautious) {:instances (set answers)})))

(defn- twin-answer
  "The answer the twin `text` gives `read`, solved by the clingo executable under the
  flags a vaelii solve passes (`clasp/solve`), with the `:among` and `:opt-strategy` of
  the read's `#solve` map.  A projected read's answer sets are the distinct projections of
  the twin's.  A `#model` read's answer says whether vaelii's answer set is among the
  twin's."
  [text names {:keys [directive arg answer-sets solve]}]
  (binding [clasp/*clasp-binary* "clingo"]
    (let [of-twin #(instances arg (map (partial sentence-of names) %))
          opts    (cond-> (select-keys solve [:among])
                    (:opt-strategy solve)
                    (assoc :opt-strategy (config/asp-opt-strategies (name (:opt-strategy solve)))))]
      (case directive
        (models model)
        (let [{:keys [status costs witnesses witness-costs]} (clasp/solve text :all-optima opts)
              pairs (cond->> (map (fn [[w c]] [(of-twin w) c])
                                  (nm/distinct-by first (map vector (map set witnesses) witness-costs)))
                      (:project solve) distinct)]
          (merge {:status status :costs costs}
                 (if (= 'models directive)
                   {:answer-sets (frequencies pairs)}
                   {:optimal? (contains? (set (map first pairs)) (set (first answer-sets)))})))
        (brave cautious)
        (let [{:keys [status costs atoms]}
              (clasp/solve text (if (= 'brave directive) :classify-supportable :classify-true) opts)]
          {:status status :costs costs :instances (of-twin atoms)})))))

(defn- agree?
  "Does `own`, the answer of a read under `#solve` map `solve`, equal `twin`?  Under a
  `:limit` n, its answer sets are n of the twin's, or all of them when the twin has fewer."
  [solve twin own]
  (if-let [n (:limit solve)]
    (let [twin-sets (:answer-sets twin) own-sets (:answer-sets own)]
      (and (= (dissoc twin :answer-sets) (dissoc own :answer-sets))
           (set/subset? (set (keys own-sets)) (set (keys twin-sets)))
           (= (min n (reduce + (vals twin-sets))) (reduce + (vals own-sets)))))
    (= twin own)))

(defn- check-program!
  "Run `<name>.vae` in `kb`, and assert each read's `[directive count costs]` equals the
  row of `expected` at its place.  The count is a `#models` read's answer sets, and a
  `#brave` or `#cautious` read's instances.  With the clingo executable at hand, assert
  each read's answer equals the twin's."
  [kb name expected]
  (let [program (run/read-run-file (str (io/file dir (str name ".vae"))))
        {:keys [refused answers]} (run/run-in kb program 64)]
    (is (nil? refused))
    (is (= expected
           (mapv (fn [{:keys [directive answer-sets answers costs]}]
                   [directive (count (or answer-sets answers)) costs])
                 answers)))
    (when clingo?
      (let [text (twin-text name) names (clingo-names program)]
        (doseq [read answers]
          (is (agree? (:solve read) (twin-answer text names read) (own-answer read))
              (str (:directive read) " " (pr-str (:arg read)) " " (pr-str (:solve read)))))))))

(deftest-kb eight-queens-has-92-solutions-under-the-pairwise-encoding
  (when asp? (check-program! kb "queens-pairwise" '[[models 92 nil]])))

(deftest-kb eight-queens-has-92-solutions-with-the-diagonals-projected
  (when asp? (check-program! kb "queens-diagonal" '[[models 92 nil]])))

(deftest-kb the-petersen-graph-has-120-three-colourings
  (when asp? (check-program! kb "colouring" '[[models 120 nil] [brave 3 nil]])))

(deftest-kb fixing-two-adjacent-colours-leaves-one-petersen-colouring-in-six
  (when asp? (check-program! kb "colouring-symmetry" '[[models 20 nil] [cautious 2 nil]])))

(deftest-kb the-cube-graph-has-12-directed-hamiltonian-cycles
  (when asp?
    (check-program! kb "hamilton" '[[models 12 nil] [cautious 8 nil] [brave 3 nil]])))

(deftest-kb the-assignment-has-three-optima-at-cost-12
  (when asp?
    (check-program! kb "assignment"
                    '[[models 3 [12]] [model 1 [12]] [brave 2 [12]] [cautious 0 [12]]])))

(deftest-kb the-sudoku-has-one-solution
  (when asp? (check-program! kb "sudoku" '[[models 1 nil]])))

(deftest-kb the-timetable-optimum-costs-1-then-2-and-two-timetables-reach-it
  (when asp? (check-program! kb "timetable" '[[models 2 [1 2]] [cautious 3 [1 2]]])))

(deftest-kb the-knapsack-optimum-leaves-value-8-behind
  (when asp? (check-program! kb "knapsack" '[[models 1 [8]] [cautious 2 [8]]])))

(deftest-kb the-timetable-under-the-bound-2-5-has-15-answer-sets-and-ignoring-its-objective-48
  (when asp?
    (check-program! kb "timetable-readings"
                    '[[models 2 [1 2]] [cautious 3 [1 2]]
                      [models 15 nil] [models 48 nil] [models 3 nil] [models 2 [1 2]]])))

(deftest-kb the-cube-cycles-projected-onto-the-edge-leaving-q0-are-three
  (when asp?
    (check-program! kb "hamilton-projected"
                    '[[models 12 nil] [cautious 8 nil] [brave 3 nil] [models 3 nil]])))
