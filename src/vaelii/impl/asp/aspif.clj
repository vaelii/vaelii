;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.aspif
  "Pure ASPIF text emitter. No vaelii deps, no I/O.

   ASPIF is the Potassco Answer Set Programming Intermediate Format, the
   ground-program protocol between gringo and clasp.  This emits the
   statements the engine's programs use: the rule line (type 1) as facts,
   choice atoms, normal rules, integrity constraints, and weight-body rules
   and constraints; minimize (2); and output (4).  Projection (3),
   externals (5), assumptions (6), heuristics (7), acyclicity edges (8) and
   type 1's disjunctive and multi-head choice heads have no encoder
   (docs/defenses.md, \"The ASPIF emitter encodes only what a program
   uses\").

   Wire format of what is emitted (line-oriented, space-separated):
     Line 1: `asp 1 0 0`
     Rule:     1 <head_type> <head_size> <head...> <body_type> <body_size> <lits...>
                 head_type = 0 disjunctive | 1 choice
                 body_type = 0 normal (list of signed literals)
                        or = 1 weight  (a cardinality/weight body)
                 body literal: +atom for positive, -atom for default-negated
     Weight body: 1 <lower_bound> <n> <lit_1> <w_1> ... <lit_n> <w_n>
                 satisfied when the summed weight of the satisfied literals is
                 at least <lower_bound>.  A cardinality constraint is the unit-weight
                 case: `k+1 <= #count{ ... }` is a weight body of bound k+1 over
                 weight-1 literals.  Emitted headless (an integrity constraint that
                 excludes any model reaching the bound) or with a head (an atom that
                 holds when the bound is reached, for a soft/minimized violation).
     Minimize: 2 <priority> <n> <lit_1> <w_1> ... <lit_n> <w_n>
     Output:   4 <str_len> <str> <n_conditions> <atoms...>
     End:      0

   Atom ids are positive integers; 0 is the terminator.  A show
   statement's length counts characters, so its text must be ASCII.

   The statement constructors return data maps, and `render` turns a
   sequence of them into the ASPIF text."
  (:require
   [clojure.string :as str]))

(defn fact
  "Unconditional fact: `atom-id` is true in every model."
  [atom-id]
  {:type :fact :atom atom-id})

(defn choice
  "Choice atom `{atom-id}.` — solver may include it or not."
  [atom-id]
  {:type :choice :atom atom-id})

(defn rule
  "Normal rule `head :- body`. `body` is a seq of signed literals
   (positive atom-id or negative for default negation)."
  [head body]
  {:type :rule :head head :body (vec body)})

(defn constraint
  "Integrity constraint `:- body`. Forbids models in which every body
   literal is satisfied."
  [body]
  {:type :constraint :body (vec body)})

(defn weight-constraint
  "Integrity constraint with a weight body: `:- lower-bound <= #sum{ ... }`.
   Forbids models in which the summed weight of the satisfied body literals
   reaches `lower-bound`. `weighted-literals` is a seq of `[literal weight]`
   pairs (a literal is a positive atom-id or negative for default negation).

   A cardinality bound is the unit-weight case: at-most-`k` over atoms `M`
   forbids `k+1` of them holding — bound `k+1` over each `[m 1]`; at-least-`k`
   forbids `|M|-k+1` of them absent — bound `|M|-k+1` over each `[-m 1]`."
  [lower-bound weighted-literals]
  {:type :weight-constraint
   :bound lower-bound
   :literals (vec weighted-literals)})

(defn weight-rule
  "Normal rule `head :- lower-bound <= #sum{ ... }` with a weight body: `head`
   holds when the summed weight of the satisfied body literals reaches
   `lower-bound`. The soft counterpart to `weight-constraint` — the derived head
   is a violation atom a `minimize` then penalizes, so breaching the bound costs
   rather than excludes."
  [head lower-bound weighted-literals]
  {:type :weight-rule
   :head head
   :bound lower-bound
   :literals (vec weighted-literals)})

(defn minimize
  "Weak constraint (minimize statement). `weighted-literals` is a seq of
   `[literal weight]` pairs. Priorities combine lexicographically when
   multiple minimize statements are present; within a priority, the
   cost is the sum of weights of satisfied literals."
  [priority weighted-literals]
  {:type :minimize
   :priority priority
   :literals (vec weighted-literals)})

(defn project
  "Projection statement over `atom-ids`, rendered `3 <n> <atom_1> … <atom_n>`: under
   `--project`, an enumeration yields one model per distinct assignment to these atoms."
  [atom-ids]
  {:type :project :atoms (vec atom-ids)})

(defn show
  "Output mapping `atom-id` to `text` in solver output. `text` must be
   ASCII and must not contain newline characters."
  [atom-id text]
  {:type :show :atom atom-id :text text})

(defn- body-tail
  "Render a normal body: `0 <n> <lit_1> ... <lit_n>`. Returns a string
   with a leading space so it can be concatenated directly to a head."
  [body]
  (if (seq body)
    (str " 0 " (count body) " " (str/join " " body))
    " 0 0"))

(defn- weight-body-tail
  "Render a weight body: `1 <lower_bound> <n> <lit_1> <w_1> ... <lit_n> <w_n>`.
   Returns a string with a leading space so it concatenates directly to a head."
  [lower-bound weighted-literals]
  (str " 1 " lower-bound " " (count weighted-literals)
       (str/join (for [[lit w] weighted-literals] (str " " lit " " w)))))

(defmulti ^:private emit-line :type)

(defmethod emit-line :fact [{:keys [atom]}]
  ;; 1 0 1 <atom> 0 0
  (str "1 0 1 " atom " 0 0"))

(defmethod emit-line :choice [{:keys [atom]}]
  ;; 1 1 1 <atom> 0 0
  (str "1 1 1 " atom " 0 0"))

(defmethod emit-line :rule [{:keys [head body]}]
  ;; 1 0 1 <head> 0 <|body|> <lits...>
  (str "1 0 1 " head (body-tail body)))

(defmethod emit-line :constraint [{:keys [body]}]
  ;; 1 0 0 0 <|body|> <lits...>
  (str "1 0 0" (body-tail body)))

(defmethod emit-line :weight-constraint [{:keys [bound literals]}]
  ;; 1 0 0 1 <lb> <n> <lit_1> <w_1> ...
  (str "1 0 0" (weight-body-tail bound literals)))

(defmethod emit-line :weight-rule [{:keys [head bound literals]}]
  ;; 1 0 1 <head> 1 <lb> <n> <lit_1> <w_1> ...
  (str "1 0 1 " head (weight-body-tail bound literals)))

(defmethod emit-line :minimize [{:keys [priority literals]}]
  ;; 2 <priority> <n> <lit_1> <w_1> ... <lit_n> <w_n>
  (str "2 " priority " " (count literals)
       (str/join (for [[lit w] literals] (str " " lit " " w)))))

(defmethod emit-line :project [{:keys [atoms]}]
  (str "3 " (count atoms) (str/join (map #(str " " %) atoms))))

(defmethod emit-line :show [{:keys [atom text]}]
  ;; 4 <len> <text> 1 <atom>   (always a single-atom condition)
  (str "4 " (count text) " " text " 1 " atom))

(defn render
  "Render a sequence of statements as a complete ASPIF program string
   with header and terminator. The input order is preserved."
  [statements]
  (apply str "asp 1 0 0\n"
         (concat (map #(str (emit-line %) "\n") statements)
                 ["0\n"])))
