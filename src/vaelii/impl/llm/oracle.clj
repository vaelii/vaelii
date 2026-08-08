;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.oracle
  "An outside judge over what the knowledge base concluded: every claim glossed into one
  English line, handed to a model, and answered *agree / disagree / unsure*.

  ## This is the other direction, and the trust runs the other way

  `vaelii.impl.llm.text` reads English **into** the KB, where the danger is a model
  writing something false into the store and the defence is a reviewer between the two.
  Here the KB is the one making claims and the model is the one being asked, so nothing
  a model says can reach the store: this namespace calls no writer, and a verdict is a
  line in a report.  A disagreement is a **finding for a person to read**, never a
  retraction, never a defeat class, and never a test failure that edits the KB to make
  the number go up.

  That is the whole of why the judge is worth having.  The engine can check that a
  conclusion follows and that a sentence is well formed; nothing in it can check that
  the knowledge is *true*, and a KB full of well-formed nonsense passes every gate this
  repo has.  An outside reader is the only instrument for that, and a model is a reader
  who will do it for two hundred claims without getting bored.

  ## The claim is glossed, and a claim the KB cannot gloss is not sent

  A model handed `(genl penguin bird)` is judging our notation.  `vaelii.impl.gloss`
  composes the English from the KB's **own** comments — the vocabulary documents itself,
  and the first clause of each comment is already a template — so what the judge sees is
  the knowledge base's sentence rather than a paraphrase somebody wrote for the prompt.
  A sentence the KB documents nothing about glosses to `:named`, which is barely more
  than the s-expression, so it is left out and counted as skipped: an unanswerable
  question dressed up as a low score measures the prompt and not the KB.

  ## A derived claim is shown its situation, and never its rule

  *Muffet is awake* is not judgeable on its own — nobody knows Muffet.  *Given that Muffet is
  a dog, Muffet is awake* is: it is the everyday question of whether that is a reasonable
  thing to say about a dog you have just been told about.  So a derived claim carries
  the facts its justification rests on, glossed the same way.

  It does **not** carry the rule, and that omission is the design.  Show the rule and
  the question becomes *does this follow*, which is validity — the one thing the engine
  already guarantees and the one thing an outside judge is not needed for.

  ## Three verdicts, because two would make the number meaningless

  Most of this KB is defaults, and a default is not a universal.  A judge forced to
  answer yes or no about *an animal is awake* will pick one and the disagreement rate
  will measure the coin.  `unsure` is where a claim that depends on particulars nobody
  supplied belongs, and the counts are reported apart so a reader can see how much of
  the answer was a shrug.

  What the rate is **not** is an accuracy: a careful judge marking a default false is
  telling you the default has exceptions, which the KB already knows and stores as a
  default for exactly that reason.  So each disagreement carries the claim's strength,
  and the disagreements — not the rate — are the output."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.gloss :as gloss]
            [vaelii.impl.llm.protocol :as proto]
            [vaelii.impl.llm.stub :as stub]))

(def default-batch-size
  "How many claims go in one turn.  Small enough that a model keeps the numbering
  straight over the whole answer, large enough that two hundred claims are ten calls and
  not two hundred model loads."
  20)

(def default-num-ctx
  "The window a judging turn asks for.  A batch of twenty one-line claims is a small
  prompt, and asking for a window the host is not already serving costs a model reload —
  which on a shared host is not a private act."
  4096)

(def max-givens
  "How many supporting facts a derived claim shows.  A conclusion resting on more than
  this has a situation nobody reads at a glance, and the line stops being one sentence."
  4)

;; ---- a stored sentex becomes an English claim ---------------------------

(defn- glossed
  "The sentex as one English line.  A rule reads back in its author's own variable names,
  which `gloss/readable` does and `gloss/text` cannot; the full stop it does not add is
  added here, so every line in a batch is punctuated the same way."
  [kb sx]
  (if (:antecedent sx)
    (update (gloss/readable kb sx) :text #(cond-> % (not (str/ends-with? % ".")) (str ".")))
    (gloss/text kb (v/readable-sentence sx))))

(defn- situation
  "One supporting fact as a given: the gloss with its apposition cut off.

  A gloss opens with the claim and then defines its terms — *Ann is a person — a human
  being — a mammal that is also …* — which is what a reader of one sentence wants and
  the wrong thing entirely in front of a question.  The definition is not part of the
  situation, and three of them make the situation unreadable.

  The full stop goes too, so `line` punctuates the join rather than inheriting whatever
  the cut left behind."
  [text]
  (-> text (str/split #" — ") first str/trim (str/replace #"\.+$" "")))

(defn- givens
  "The facts a derived claim rests on, glossed — its justification's antecedents, one
  level down and no further.

  Two things are left out.  **The rule**, because showing it turns the question from *is
  this so* into *does this follow*.  And **the taxonomy edges** it fired through: a
  `genl` edge is vocabulary rather than a fact about anybody, and *every mammal is an
  animal* in front of a question about Ann is the rule wearing a different hat."
  [kb handle]
  (let [tree (v/why kb handle)
        because (:because (first (:support tree)))]
    (into []
          (comp (remove :cycle?)
                (keep (fn [{:keys [sentence]}]
                        (when (and sentence
                                   (not (contains? #{'genl 'genlContext}
                                                   (when (sequential? sentence) (first sentence)))))
                          (let [{:keys [text source]} (gloss/text kb sentence)]
                            (when (not= :named source) (situation text))))))
                (distinct)
                (take max-givens))
          because)))

(defn claims
  "`handles` -> the claim maps a judging turn is built from, sorted by content.

  Sorted by the **glossed text**, not by handle: two KBs holding the same knowledge in a
  different order must produce the same prompt, or a run is not comparable with the one
  before it.  Each map carries what a reader of the report needs — the sentence, its
  context, whether anybody asserted it, the strength it is held at, and the situation a
  derived one rests on.

  `:source` is the gloss's, and `judgeable?` reads it."
  [kb handles]
  (let [made (keep (fn [h]
                     (when-let [sx (v/sentex kb h)]
                       (let [{:keys [text source]} (glossed kb sx)
                             premise? (v/premise? kb h)]
                         {:handle   h
                          :sentence (v/readable-sentence sx)
                          :context  (:context sx)
                          ;; the JTMS's answer, not the sentex's: a derived sentex
                          ;; carries no strength of its own, and reading the empty slot
                          ;; as monotonic would label every default conclusion as a
                          ;; claim without exceptions — the one thing a reader of a
                          ;; disagreement most needs to be right
                          :strength (v/defeat-class kb h)
                          :premise? premise?
                          :text     text
                          :source   source
                          :givens   (if premise? [] (givens kb h))})))
                   handles)]
    (into [] (map-indexed #(assoc %2 :index %1))
          (sort-by (juxt :text #(pr-str (:sentence %))) made))))

(defn judgeable?
  "Is there an English sentence here to judge?  A gloss that is entirely `:named` is the
  formal sentence with its symbols spaced out, and asking about it measures the prompt."
  [claim]
  (contains? #{:composed :partial} (:source claim)))

;; ---- the output contract ------------------------------------------------

(def output-schema
  "The JSON schema decoding is constrained to.  `item` is the number of the claim being
  answered, and it is what makes a skipped claim visible: an answer with fifteen verdicts
  to twenty claims has five gaps, and gaps are reported rather than read as agreement."
  {"type" "object"
   "properties"
   {"verdicts"
    {"type" "array"
     "description" "One entry per numbered statement, in the order they were given."
     "items"
     {"type" "object"
      "properties"
      {"item" {"type" "integer"
               "description" "The number in brackets at the start of the statement."}
       "verdict" {"type" "string" "enum" ["true" "false" "unsure"]
                  "description" (str "true = an ordinary person would agree; false = they "
                                     "would say it is wrong; unsure = it depends on things "
                                     "you were not told.")}
       "note" {"type" "string"
               "description" "One short clause, and only where it is worth reading."}}
      "required" ["item" "verdict"]}}}
   "required" ["verdicts"]})

(def system-prompt
  "The instruction half, which never varies — so a provider that caches a system turn
  caches this one across every batch of a run."
  (str
   "You are checking a knowledge base of ordinary common sense. Each numbered statement "
   "below is something the knowledge base holds. For each one, say whether an ordinary "
   "careful person would agree.\n\n"
   "- **true** — they would agree it is so, or so as a general rule.\n"
   "- **false** — they would say it is wrong.\n"
   "- **unsure** — it turns on particulars you were not given, or you do not know.\n\n"
   "**Judge the claim, not the wording.** These sentences are composed by a machine from "
   "a formal representation. Clumsy phrasing is not a reason to call one false; only the "
   "claim itself is.\n\n"
   "**A general rule is true even where it has exceptions.** *Birds fly* is true as a "
   "general rule though penguins do not. Answer false only when the general case itself "
   "is wrong, not when you can think of an exception to it.\n\n"
   "**Where a statement has a `Given:` part, take that part as true** and judge only the "
   "`Claim:` after it. The names in it are made-up things you have just been introduced "
   "to, and everything you know about them is what the statement says.\n\n"
   "Answer every statement, by its number. A short `note` on anything you called false "
   "is worth more to the reader than the verdict on its own."))

;; ---- the turn -----------------------------------------------------------

(defn line
  "One claim as the prompt shows it: its number, the situation it rests on when it has
  one, and the claim itself.

  Each given keeps the capital it was composed with — lower-casing an opening `Muffet` to
  make the join read better would misspell the vocabulary, which is the one thing a gloss
  may not do."
  [{:keys [index text givens]}]
  (str "[" index "] "
       (if (seq givens)
         (str "Given: " (str/join ". " givens) ". Claim: " text)
         text)))

(defn user-turn
  "The volatile half: the numbered claims and nothing else.  No vocabulary card and no
  formal sentences — a judge shown the s-expression would answer about the s-expression."
  [claims]
  (str "## Statements (" (count claims) ")\n\n"
       (str/join "\n" (map line claims))))

(def ^:private fenced-block #"(?s)```(?:json|edn|clojure|clj|text)?\s*\n?(.*?)```")

(defn- unfence
  "The contents of a markdown fence, when the answer is wrapped in one.  Models fence
  unprompted, including while decoding under a schema that cannot express a fence."
  [text]
  (or (second (re-find fenced-block (str text))) (str text)))

(def ^:private verdict-words
  {"true" :agrees "yes" :agrees "agree" :agrees
   "false" :disputes "no" :disputes "disagree" :disputes
   "unsure" :unsure "unknown" :unsure "maybe" :unsure})

(defn parse-verdicts
  "A model's answer -> `{item -> {:verdict :note}}`.

  Tolerant in the three ways this answer goes wrong and strict in the one that matters:
  a fence is stripped, a word outside the enum reads as `:unsure` rather than throwing,
  and a repeated item keeps the **first** answer — but an item number that names no claim
  is dropped, because a verdict that cannot be attached to a claim is not evidence about
  anything."
  [text n]
  (let [parsed (try (json/parse-string (unfence text)) (catch Exception _ nil))
        items  (when (map? parsed) (get parsed "verdicts"))]
    (reduce (fn [acc item]
              (let [i (get item "item")
                    w (some-> (get item "verdict") str str/trim str/lower-case)]
                (if (and (int? i) (< -1 i n) (not (contains? acc i)))
                  (assoc acc i {:verdict (get verdict-words w :unsure)
                                :note (some-> (get item "note") str str/trim not-empty)})
                  acc)))
            {}
            (filter map? (when (sequential? items) items)))))

(defn- request
  [claims {:keys [model num-ctx max-tokens]}]
  (cond-> {:system [{:text system-prompt :cache? true}]
           :messages [{:role "user" :content (user-turn claims)}]
           :format output-schema
           :num-ctx (or num-ctx default-num-ctx)}
    model      (assoc :model model)
    max-tokens (assoc :max-tokens max-tokens)))

(defn judge-batch
  "One turn over one batch of claims -> the claims with `:verdict` and `:note` on them.
  A claim the answer skipped comes back `:unanswered`, which is a different thing from
  every verdict and is counted as one."
  [claims {:keys [provider] :as opts}]
  (let [provider (or provider (stub/provider))
        response (proto/complete provider (request claims opts))
        answers  (parse-verdicts (proto/text response) (count claims))]
    {:claims (mapv (fn [{:keys [index] :as claim}]
                     (merge claim (get answers index {:verdict :unanswered})))
                   claims)
     :usage (:usage response)
     :model (:model response)}))

(defn judge
  "Judge every claim, in batches.  Returns

      {:judged   [claim + :verdict + :note …]   ; sorted as `claims` sorted them
       :skipped  [claim …]                      ; no English to judge
       :batches n :usage {…} :model \"…\"}

  `opts`: `:provider` (default: the offline stub), `:model`, `:num-ctx`, `:max-tokens`,
  `:batch-size`.

  Renumbering per batch is deliberate: each turn's item numbers start at zero, so a
  model that answers `item: 3` in the fourth batch has answered the fourth claim of that
  batch and not the fourth of the run.  Nothing here writes to a KB — the claims arrived
  as data and leave as data."
  ([claims] (judge claims {}))
  ([claims {:keys [batch-size] :as opts}]
   (let [{yes true no false} (group-by judgeable? claims)
         batches (partition-all (or batch-size default-batch-size) yes)
         runs (mapv #(judge-batch (into [] (map-indexed (fn [i c] (assoc c :index i))) %) opts)
                    batches)]
     {:judged (into [] (mapcat :claims) runs)
      :skipped (vec no)
      :batches (count runs)
      :model (:model (first runs))
      :usage (apply merge-with + {} (keep :usage runs))})))

;; ---- what came back -----------------------------------------------------

(defn agreement
  "The arithmetic over a judged set.

  Two rates, because they answer different questions.  `:rate` is agreement over every
  claim that was put, which is the one that moves when the KB changes.  `:decided` is
  agreement over the ones the judge committed on, which is the one to quote when a model
  shrugs at half of them.  Both are `nil` rather than zero over an empty denominator — a
  rate over nothing is not a bad score, it is no score."
  [{:keys [judged skipped]}]
  (let [by (frequencies (map :verdict judged))
        agreed (get by :agrees 0)
        disputed (get by :disputes 0)
        total (count judged)
        decided (+ agreed disputed)]
    {:total total
     :agreed agreed
     :disputed disputed
     :unsure (get by :unsure 0)
     :unanswered (get by :unanswered 0)
     :skipped (count skipped)
     :rate (when (pos? total) (double (/ agreed total)))
     :decided (when (pos? decided) (double (/ agreed decided)))
     :disagreements (vec (filter #(= :disputes (:verdict %)) judged))}))

(defn- pct [x] (if x (format "%.0f%%" (* 100.0 x)) "—"))

(defn report
  "The whole result as text: the counts, then every disagreement with the claim's
  strength and the judge's note.

  The disagreements are the report and the rate is the index into them, so they are
  printed in full rather than summarized.  A `:default` beside one is not an excuse for
  it — it is the fact a reader needs to decide whether the judge found a bad claim or a
  claim that is simply defeasible, and those want different work."
  [result]
  (let [{:keys [total agreed disputed unsure unanswered skipped rate decided
                disagreements]} (agreement result)]
    (str "claims judged " total
         "  agreed " agreed " (" (pct rate) ")"
         "  disputed " disputed
         "  unsure " unsure
         (when (pos? unanswered) (str "  unanswered " unanswered))
         (when (pos? skipped) (str "  not glossable " skipped))
         "\nagreement over the decided ones: " (pct decided)
         (when (seq disagreements)
           (str "\n\ndisputed:\n"
                (str/join "\n"
                          (for [{:keys [text strength note sentence]} disagreements]
                            (str "  - " text
                                 " [" (name (or strength :out)) "] "
                                 (pr-str sentence)
                                 (when note (str "\n      " note))))))))))
