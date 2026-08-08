;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.text
  "The document-scoped prompt: **text in, candidates out — never knowledge in.**

  `vaelii.impl.gloss` composes English *out of* the KB and says why that direction is the
  dangerous one: nothing in the engine can check that a sentence means what a text said.
  This namespace is the other direction, and it has to answer that argument rather than
  ignore it, because every check the engine has passes on a correct-looking translation of
  the wrong claim — naming, well-formedness, argument types and disjointness all read the
  *sentence*.  So what is built here is a **candidate generator with a reviewer between it
  and the store**, and every decision below follows from that:

  * a candidate is a `[sentence context opts]` entry, which is the shape
    `vaelii.core/edit!` already takes and the browser's editor already parses — so a
    proposal lands as a reviewable diff and there is no second write path;
  * a candidate carries the **span** of the text it came from, so an accepted sentence is
    auditable back to the sentence that produced it;
  * a candidate is `:default`, never `:monotonic` unless the reader says so — a translated
    guess asserted as known-true would defeat hand-written defaults;
  * what the pipeline **could not** translate is part of the answer (`coverage`), because a
    reader who is shown only the two-thirds that worked reads it as a reader that
    understood the document.

  **Where the boundary is.**  Nothing here is in `vaelii.core`, and nothing here writes.
  Like `web` / `serve` / `llm`, this is an application over the engine: the engine's
  contribution is the critic (`check-edit`), the vocabulary (the taxonomy and the
  declarations), the provenance side map, and the equality partition — all of them public
  reads that existed already.  See docs/reading.md.

  ## Resolution is the problem; parsing is not

  A pipeline that coins `has_black_and_white_feathers` for every sentence produces
  fragmentation rather than knowledge, and no naming check refuses it (docs/naming.md says
  so in as many words).  So the document's own words are resolved against the vocabulary
  the KB already has **before** a model is asked anything:

  * `spellings` turns each run of the document's words into the symbols a KB term could be
    spelled as — *prepared for winter* into `preparedForWinter` and `prepared_for_winter`,
    *Muffet* into `Muffet` — and `known` asks the KB which of them it has.  Generating and
    asking runs the *opposite* way from inverting the KB's vocabulary into the words each
    term is written with, which is the one read here that would grow with the KB;
  * `resolve-in` walks the document longest-run-first and non-overlapping, so a compound
    predicate is not shredded into the words its name is made of;
  * every resolved term is the equality partition's `representative`, so a word spelled at
    a retired name resolves to the term that name was merged into.

  What resolves becomes the vocabulary card (`document-inventory`), which is the
  prevention half of the fragmentation guard; the detection half is
  `vaelii.impl.llm.inventory/coined`, unchanged and shared with the other three paths."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.llm.inventory :as inventory]
            [vaelii.impl.llm.selection :as selection]))

;; ---- the document as spans ----------------------------------------------

(defn segments
  "A document cut into sentences: `[{:index i :text \"…\" :span [start end]} …]`.

  The span is what everything downstream is for — `(subs doc start end)` is the segment's
  text, exactly, so an accepted candidate points back at characters rather than at a
  paraphrase.  A test holds that identity.

  Cut at a run of `.`/`!`/`?` followed by whitespace or the end of the document, which is
  crude and deliberately so: an abbreviation splits a segment in two, which costs a
  narrower span and no correctness, while a cleverer splitter would need a model and put
  one on the *reading* side of the pipeline where there is nothing to check it.  A
  semicolon or a colon does **not** cut — a segment may carry several claims, and which
  claim came from which clause is not something the span can honestly say."
  [doc]
  (let [doc (str doc)
        ends (let [m (re-matcher #"[.!?]+(?=\s|$)" doc)]
               (loop [acc []] (if (.find m) (recur (conj acc (.end m))) acc)))
        ends (if (or (empty? ends) (< (peek ends) (count doc)))
               (conj ends (count doc))
               ends)]
    (vec (->> (map vector (cons 0 ends) ends)
              (keep (fn [[from to]]
                      (let [raw   (subs doc from to)
                            lead  (- (count raw) (count (str/triml raw)))
                            start (+ from lead)
                            end   (+ start (count (str/trim raw)))]
                        (when (< start end)
                          {:text (subs doc start end) :span [start end]}))))
              (map-indexed (fn [i s] (assoc s :index i)))))))

;; ---- what the document's own words already name -------------------------

(def ^:private max-phrase
  "The longest run of words looked up as one term.  `betterPreparedThan` is four words and
  `quantityGreaterThanOrEqual` is five, so a shorter window would miss the compound
  predicates that are exactly the ones worth reusing."
  5)

(defn- singular
  "A word with its plural taken off, or nil when it has none.  English plurals, badly and on
  purpose: a document says *lions* where the vocabulary says `lion`, and getting the regular
  case is most of the difference between resolving and not.  An irregular plural (*mice*)
  simply does not resolve, which costs a reuse and never a wrong answer."
  [w]
  (cond
    (re-find #"[^aeiou]ies$" w) (str (subs w 0 (- (count w) 3)) "y")
    (re-find #"(?:ch|sh|ss|x|z)es$" w) (subs w 0 (- (count w) 2))
    (re-find #"[^s]s$" w) (subs w 0 (dec (count w)))))

(defn spellings
  "The symbols a run of words could be a KB term spelled as.

  The KB reads a term's role off its spelling, so a phrase has one candidate per
  convention: *prepared for winter* could be the predicate `preparedForWinter` or the type
  `prepared_for_winter`, and one word could be `lion`, `Lion` or its singular.  Generating
  the spellings and asking the KB which exist is the whole of resolution — the alternative,
  inverting the KB's vocabulary into the words each term is written with, is the one read
  here that would grow with the knowledge base.

  Nothing is filtered by plausibility: `allThroughThe` is generated and the KB says no, at
  the cost of one set lookup."
  [words]
  (when (seq words)
    (let [joined (str/join "_" words)
          camel  (str (first words)
                      (str/join (map str/capitalize (rest words))))]
      (distinct
       (concat [(symbol camel) (symbol joined)]
               (when (= 1 (count words))
                 (let [w (first words)]
                   (concat [(symbol (str (str/upper-case (subs w 0 1)) (subs w 1)))]
                           (when-let [s (singular w)]
                             [(symbol s)
                              (symbol (str (str/upper-case (subs s 0 1)) (subs s 1)))])))))))))

(defn- segment-words
  "A segment's words as `[word start end]`, lowercased, with **absolute** spans — so a
  resolution points into the document the same way a candidate's provenance does.
  Punctuation and digits end a word; an apostrophe does not, so *hunter's* is one word and
  resolves (or fails to) as one."
  [{:keys [text span]}]
  (let [base (first span)
        m    (re-matcher #"[A-Za-z][A-Za-z']*" text)]
    (loop [acc []]
      (if (.find m)
        (recur (conj acc [(str/lower-case (.group m)) (+ base (.start m)) (+ base (.end m))]))
        acc))))

(defn- word-runs
  "Every run of up to `max-phrase` consecutive words in a segment, as word vectors — what
  `spellings` is generated over."
  [seg]
  (let [ws (mapv first (segment-words seg))
        n  (count ws)]
    (for [i (range n)
          len (range 1 (inc (min max-phrase (- n i))))]
      (subvec ws i (+ i len)))))

(defn known
  "The generated spellings the KB actually has a term for, as `{spelling representative}`.

  **One roster read, not a probe apiece.**  `vaelii.impl.llm.inventory/unknown-terms` asks
  the index's O(1) roots first because it is asked about a *proposal*, where nearly every
  functor is already known; a document is the opposite case — a hundred words generate
  hundreds of spellings and almost none of them name anything — so the roots would be
  probed hundreds of times to answer no, where the roster answers all of them at once.

  A term is kept only if its spelling gives it a role a candidate could use: a context is
  dropped (candidates are filed in the caller's context, never one the text names) and so is
  the structural frame.  Every value is the equality partition's `representative`, so a word
  spelled at a retired name resolves to the term that name was merged into."
  [kb spellings]
  (let [roster (set (v/terms kb))]
    (into {} (for [s (distinct spellings)
                   :when (and (contains? roster s)
                              (#{:individual :type :predicate} (v/term-role s))
                              (not (inventory/structural-functor? s)))]
               [s (v/representative kb s)]))))

(defn resolve-in
  "The resolutions in `segs` against an already-computed `known` map, as
  `[{:surface \"prepared for winter\" :term preparedForWinter :segment 0 :span [12 31]} …]`.

  Longest run first and **non-overlapping**: *prepared for winter* wins over *winter*, so a
  compound predicate is not shredded into the words its name is made of.  Within one length
  the spelling order of `spellings` decides, which puts the predicate reading ahead of the
  type reading — the same precedence the naming invariants give a bare lowercase word.

  Separate from `resolutions` so the walk is testable without a KB: everything here is
  arithmetic over the segments and the map."
  [known segs]
  (vec (for [{:keys [index] :as seg} segs
             :let [ws (segment-words seg)
                   n  (count ws)]
             r (loop [i 0, out []]
                 (if (>= i n)
                   out
                   (if-let [hit (first (for [len (range (min max-phrase (- n i)) 0 -1)
                                             :let [words (mapv first (subvec ws i (+ i len)))
                                                   t (some known (spellings words))]
                                             :when t]
                                         {:surface (str/join " " words) :term t :len len
                                          :span [(nth (nth ws i) 1)
                                                 (nth (nth ws (+ i len -1)) 2)]}))]
                     (recur (long (+ i (:len hit))) (conj out (dissoc hit :len)))
                     (recur (inc i) out))))]
         (assoc r :segment index))))

(defn resolutions
  "Every term the document's own words already name, in document order.

  This is the whole of what the pipeline knows about the text before a model is asked
  anything, and it is what the vocabulary card is built from — the prevention half of the
  fragmentation guard.  Two passes over the document and **one** KB read: every spelling the
  document could contain is generated first, `known` answers all of them together, and the
  walk is then arithmetic."
  [kb segs]
  (resolve-in (known kb (mapcat #(mapcat spellings (word-runs %)) segs)) segs))

;; ---- the vocabulary card for a document ---------------------------------

(defn declared-in
  "Every predicate declared **in `context`'s cone**, as `[[predicate arity] …]` — its
  `unaryPredicate` / `binaryPredicate` / `ternaryPredicate` memberships, read at that
  context so the answer is what a sentex filed there would be allowed to use.

  Scoped where `vaelii.impl.llm.inventory/declared-arities` is not, and that is the
  difference that matters here: a candidate is filed in one context, and the vocabulary of
  the context it lands in is precisely the vocabulary it may reuse.  What this puts on
  the card is **names and shapes**, never content — a predicate's declaration says it exists
  and takes two arguments, and says nothing about what is true of anything.

  **Ordered nearest context first**, because that is where a cap has to cut.  The cone
  of a leaf context runs from the story it is about up to the vocabulary head, and a
  predicate the story's own theory declares is worth more to a reader of that story than
  one `CoreContext` declares — so the cone is sorted by how much each context sees, which
  is largest at the leaf and smallest at the head.  Alphabetical within one context, so the
  order is a function of the taxonomy and never of arrival.

  The cone is walked term by term because a read at a *ground* context is exact-context:
  `sentexes-matching` at `LionMouseContext` answers about that context alone, and what the
  context *sees* is `context-up`, a cached closure lookup.  So this is one narrow read per
  context in the cone."
  [kb context]
  (let [depth  #(- (count (v/context-up kb %)))
        cone   (sort-by (juxt depth str) (v/context-up kb context))]
    (vec (distinct
          (for [ctx cone
                [pred n] (sort-by (comp str key) inventory/predicate-type-arities)
                p (sort (for [{:keys [sentence]} (v/sentexes-matching kb (list pred '?p) ctx)]
                          (nth sentence 1)))]
            [p n])))))

(defn document-inventory
  "The vocabulary a document should be written in, in
  `vaelii.impl.llm.inventory/inventory`'s shape so its renderer takes it unchanged:
  `{:types :relations :structural :dropped}`.

  Three relevance tiers, in the order a token cap should cut them from the bottom:

  1. what the document's **own words** resolved to — the vocabulary the text demonstrably
     wants, and the reason resolution runs before the model is asked anything;
  2. what an `argIsa` **licenses** for a resolved type, so a document about a mouse is
     offered the relations a mouse can stand in;
  3. everything else `context` **declares**, nearest context first (`declared-in`) —
     the vocabulary of the theory the candidates land in.  Last because it is the least
     targeted, and included at all because a document rarely spells a predicate the way the
     KB does: *repay the kindness* does not resolve `repaidKindness`, and a reader who
     cannot see that name coins a synonym for it.

  The type block is the resolved types plus one step up the taxonomy, so `mouse` puts
  `animal` on the card and the block reads as a hierarchy.

  **Cost is the vocabulary's, not the document's and not the KB's** — the same shape
  `vaelii.impl.llm.inventory/inventory` has, and the same reason: the taxonomy's node set,
  the arity declarations, one `comment` read per rendered term, and one narrow `argIsa`
  query per resolved type and per rendered predicate.  Nothing here walks facts.  The
  *card* tracks the document (tiers 1 and 2 are seeded by what resolved); the *reads* track
  how much vocabulary the KB has.

  `opts`: `:max-relations` (60), `:max-types` (60), `:max-genls` (4).  Smaller than the page
  path's caps by design: a document resolves many terms where a page has one, and the window
  belongs to the text."
  ([kb resolved context] (document-inventory kb resolved context {}))
  ([kb resolved context {:keys [max-relations max-types max-genls]
                         :or {max-relations 60 max-types 60 max-genls 4}}]
   (let [seeds     (distinct (map :term resolved))
         all-types (set (v/types kb))
         local     (declared-in kb context)
         arities   (into (inventory/declared-arities kb) local)
         struct    (inventory/structural-terms kb)
         seed-set  (set seeds)
         nearest   #(sort-by (partial inventory/specificity kb) %)
         up        (for [t seeds :when (all-types t)
                         g (take max-genls (nearest (disj (set (v/genls kb t)) t)))]
                     g)
         types     (distinct (concat (filter all-types seeds) (sort (distinct up))))
         head-only? #(and (struct %) (not (seed-set %)))
         domain?   #(and (not (all-types %)) (not (head-only? %))
                         (not (inventory/structural-functor? %)))
         licensed  (for [t types
                         {:keys [sentence]} (v/sentexes-matching kb (list 'argIsa '?p '?n t) '?ctx)
                         :let [p (nth sentence 1)]
                         :when (domain? p)]
                     p)
         relations (distinct (concat (filter domain? seeds)
                                     (sort (distinct licensed))
                                     ;; `declared-in`'s own order, which is the relevance
                                     ;; order — nearest context first
                                     (filter domain? (map first local))))
         kept      (take max-relations relations)
         shown     (take max-types types)]
     {:term nil
      :types (vec (for [t shown]
                    {:type t
                     :parent (first (nearest (disj (set (v/genls kb t)) t)))
                     :doc (first (core-context/comment-of kb t))}))
      :relations (vec (for [p kept] (inventory/predicate-shape kb p (arities p))))
      :structural (vec (for [p inventory/structural-predicates
                             :when (arities p)]
                         (inventory/predicate-shape kb p (arities p))))
      :dropped {:relations (max 0 (- (count relations) (count kept)))
                :types (max 0 (- (count types) (count shown)))}})))

;; ---- the output contract ------------------------------------------------

(def output-schema
  "The JSON schema decoding is constrained to — **the contract on this path**, for the page
  path's measured reason: on generation a schema is what makes a local model answer in
  s-expressions at all rather than in an essay.

  Two fields do work no other path needs.  **`segment`** is the index of the sentence the
  candidate came from, and it is how the span reaches provenance — the model is the only
  thing that knows which sentence it was translating, and asking for the offsets instead
  would be asking it to count characters.  **`untranslated`** is where a sentence it could
  not formalize goes, with a reason; the coverage report does not trust it (a segment that
  produced no candidate is uncovered whether the model said so or not), but a stated reason
  is worth more to a reviewer than an inferred silence."
  {"type" "object"
   "properties"
   {"candidates"
    {"type" "array"
     "description" (str "One entry per formal claim the text supports. Several may come "
                        "from one sentence, and a sentence may support none.")
     "items"
     {"type" "object"
      "properties"
      {"sentence" {"type" "string"
                   "description" (str "One s-expression and nothing else, e.g. (dog Muffet) "
                                      "or (implies (dog ?x) (mortal ?x))")}
       "segment" {"type" "integer"
                  "description" "The number of the numbered sentence this came from."}
       "confidence" {"type" "string" "enum" ["high" "medium" "low"]
                     "description" (str "high = the text says exactly this; medium = a fair "
                                        "reading; low = a guess worth a reviewer's time.")}
       "strength" {"type" "string" "enum" ["monotonic" "default"]
                   "description" (str "Omit unless the text states the claim as holding "
                                      "without exception.")}}
      "required" ["sentence" "segment"]}}
    "untranslated"
    {"type" "array"
     "description" "Every numbered sentence you could not turn into a claim, and why."
     "items" {"type" "object"
              "properties" {"segment" {"type" "integer"}
                            "reason" {"type" "string"
                                      "description" "One short clause."}}
              "required" ["segment"]}}
    "notes" {"type" "string"
             "description" "Vocabulary you had to invent, or anything you were unsure of."}}
   "required" ["candidates"]})

;; ---- the instruction half -----------------------------------------------

(def ^:private worked-example
  "One numbered passage and the whole answer to it, shown rather than described.

  It carries four things prose alone does not move a model on: that a general claim in the
  text is a **rule** and a particular one is a fact, that a character introduced by its
  kind needs a name minted for it and then *kept* across sentences, that the segment number
  rides on every candidate, and that a sentence carrying no claim is reported rather than
  dropped."
  (str "### Example\n\n"
       "Text:\n\n"
       "    [0] A dog belonging to Ann lived in the village.\n"
       "    [1] It was a fine morning.\n"
       "    [2] Every dog is an animal, and animals are mortal.\n\n"
       "Your whole answer:\n\n"
       "    {\"candidates\": [\n"
       "       {\"sentence\": \"(dog Dog1)\",              \"segment\": 0, \"confidence\": \"high\"},\n"
       "       {\"sentence\": \"(ownedBy Dog1 Ann)\",       \"segment\": 0, \"confidence\": \"high\"},\n"
       "       {\"sentence\": \"(genl dog animal)\",        \"segment\": 2, \"confidence\": \"high\"},\n"
       "       {\"sentence\": \"(implies (animal ?x) (mortal ?x))\", \"segment\": 2, \"confidence\": \"medium\"}],\n"
       "     \"untranslated\": [{\"segment\": 1, \"reason\": \"scene-setting, no claim\"}]}\n\n"
       "`Dog1` is minted because the text names no dog — and it is used again in the second "
       "candidate, because both are about the same animal. Sentence 1 states nothing, so it "
       "is reported rather than left out."))

(def system-prompt
  "The instruction half — static, because everything about the KB and the document rides in
  the user turn.

  What it spends its tokens on is the four failures this direction has that the other three
  do not: inventing vocabulary the card already holds (the shared failure, and the one the
  card is there to prevent), stating a general claim as a fact with a loose variable,
  introducing a character twice under two names, and quietly translating what the text did
  not say.  The last is the one no check downstream can catch, so it is the one stated
  most plainly: the reader would rather have a sentence reported as untranslatable than a
  fluent sentence that is not in the text."
  (str
   "You turn English into candidate assertions for a formal common-sense knowledge base. "
   "You are given a document cut into numbered sentences, the vocabulary the knowledge "
   "base already has, and the context the candidates would be filed in.\n\n"
   "**You are proposing, not recording.** Every candidate is reviewed by a person before "
   "anything is stored, so a claim you are unsure of is worth proposing at low confidence "
   "— and a claim the text does not make is worth nothing at all. Never write a sentence "
   "the text does not support, however true it seems.\n\n"
   "A claim is one Lisp s-expression, in one of these shapes:\n\n"
   "    (<type> <Individual>)                                a thing's kind\n"
   "    (<relation> <Individual> <Individual>)               a fact about two things\n"
   "    (not (<relation> <Individual> <Individual>))         a fact that is false\n"
   "    (genl <subtype> <supertype>)                         every A is a B\n"
   "    (implies (<type> ?x) (<property> ?x))                a general claim about a kind\n"
   "    (implies (and (<p> ?x ?y) (<q> ?y)) (<r> ?x ?y))     a general claim joining two\n\n"
   "**Write no context, and no `ist`.** Every candidate is filed in the context named in "
   "the user turn. `(ist SomeContext ...)` means *file this in SomeContext* — it is not a "
   "claim, it is a filing instruction, and writing one puts your sentence somewhere the "
   "reviewer is not looking. Write the bare sentence.\n\n"
   "**A general claim in the text is a rule, not a fact.** \"Whoever is spared repays the "
   "kindness\" is `(implies (spared ?x ?y) (repaidKindness ?y ?x))`. A bare "
   "`(repaidKindness ?x ?y)` with variables and no `implies` around it is rejected, and so "
   "is a rule whose conclusion uses a variable no condition introduced.\n\n"
   "**Name each character once and keep the name.** A text saying \"a lion\" gives you no "
   "name, so mint one — `Lion1` — write `(lion Lion1)`, and use `Lion1` in every later "
   "candidate about that lion. Two names for one character makes every claim about it "
   "unjoinable. A character the text *does* name keeps that name.\n\n"
   "Naming is mechanical and enforced:\n\n"
   "| role | form | example |\n"
   "|---|---|---|\n"
   "| predicate | camelCase | `spared`, `livesIn` |\n"
   "| individual | CapitalCamelCase, no underscore | `Lion1`, `Ann` |\n"
   "| type | snake_case, used as a **unary** predicate | `mouse`, `physical_object` |\n\n"
   "**Reuse the vocabulary on the card, and put the detail in arguments.** A predicate "
   "invented for one sentence joins no rule and matches nothing: write "
   "`(livesIn ?x Antarctica)`, never `(lives_in_antarctica ?x)`. Before writing any "
   "predicate, look for it on the card under a plainer name — `can…`, `has…`, `is…` and "
   "`…able` are almost always something the card already has. Say in `notes` when you had "
   "to invent one.\n\n"
   "**Report what you cannot translate.** A sentence that sets a scene, describes a "
   "feeling, or makes a claim you have no vocabulary for goes in `untranslated` with a "
   "reason. Leaving it out silently is the one thing that would make this answer "
   "misleading.\n\n"
   worked-example))

(defn numbered
  "The document as the prompt shows it: one numbered line per segment.  Numbering is what
  the `segment` field on every candidate refers back to, so it is the whole of how a span
  survives the round trip through a model."
  [segs]
  (str/join "\n" (for [{:keys [index text]} segs]
                   (str "[" index "] " text))))

(defn user-turn
  "The volatile half: the numbered document, the vocabulary its own words resolved to, the
  context candidates are filed in, and the reader's instruction if they gave one.

  The document comes **first** and the vocabulary after it, the opposite of the page path.
  The card is here to be consulted while translating rather than to be summarized, and a
  reader's instruction — when there is one — goes last so it is the newest thing in the
  window."
  ([kb segs resolved context instruction] (user-turn kb segs resolved context instruction {}))
  ([kb segs resolved context instruction opts]
   ;; A document card lists a whole context's vocabulary where a page card lists one
   ;; term's neighbourhood, so each line gets a shorter reminder: the *signature* is what
   ;; makes a predicate reusable, and 40 predicates each carrying 140 characters of prose
   ;; spends the window on documentation nobody reads while translating.
   (let [opts (merge {:max-doc-chars 100} opts)
         inv  (document-inventory kb resolved context opts)]
     (str "## The document (" (count segs) " sentences)\n\n"
          (numbered segs)
          "\n\n## Candidates are filed in " (selection/tick context) "\n\n"
          "Write no context — every candidate is filed there.\n\n"
          "## Vocabulary already in this knowledge base\n\n"
          (inventory/render inv opts)
          (when-let [words (seq (distinct (map :surface resolved)))]
            (str "\n\nWords in the document that already name something above: "
                 (str/join ", " (map #(str "*" % "*") (sort words))) "."))
          (when-not (str/blank? (str instruction))
            (str "\n\n## The reader's instruction\n\n" (str/trim (str instruction))))))))

;; ---- a read candidate becomes an entry ----------------------------------

(def confidence-ranks
  "The three tiers a candidate can claim, as the number provenance records.

  A **rank, not a probability**: it orders a review queue and nothing else reads it.  A
  number rather than the keyword because ordering is the whole job, and belief never reads
  provenance at all — so this cannot become a defeat class even by accident.  There are two
  strength classes and there will not be a third (docs/nmtms.md); a parser's confidence
  lives here instead."
  {:high 0.9 :medium 0.6 :low 0.3})

(defn candidate-entry
  "One read candidate -> the `[sentence context opts]` entry `vaelii.core/edit!` takes.

  `opts` carries the **provenance** — `{:source :segment :span :confidence}` — which is the
  reason to prefer this over a script that pastes facts in: the per-handle provenance map
  is open and unread by belief (docs/storage.md), so an accepted sentence stays auditable
  back to the characters it came from.  A candidate whose `segment` names no sentence gets
  no span and says so with `:segment nil`, rather than being given a plausible one.

  `:strength` is omitted unless the candidate claimed `:monotonic`, so a candidate is
  `:default` by construction: a translated guess that defeated a hand-written default
  would be the worst outcome this pipeline has available."
  [{:keys [sentence segment confidence strength]} context source segs]
  (let [seg  (first (filter #(= segment (:index %)) segs))
        prov (cond-> {:source source :segment (:index seg)}
               seg        (assoc :span (:span seg))
               confidence (assoc :confidence (confidence-ranks confidence)))]
    [sentence context (cond-> {:provenance prov}
                        (= :monotonic strength) (assoc :strength :monotonic))]))

(defn entry-provenance
  "The provenance map on an entry built by `candidate-entry`, or nil."
  [entry]
  (:provenance (nth entry 2 nil)))

;; ---- what it could not translate ---------------------------------------

(defn coverage
  "Which of the document's sentences the reader translated, and which it did not:

      {:segments 5 :covered 4
       :uncovered [{:index 1 :span [42 61] :text \"It was a fine morning.\"
                    :reason \"scene-setting, no claim\"}]}

  **Computed, not reported.**  A segment is uncovered when no candidate names it, whatever
  the model listed in `untranslated` — a model that quietly drops a third of a document and
  says nothing would otherwise read as one that understood it.  A stated reason is attached
  where there is one and the segment really did produce nothing; where the model claimed a
  sentence was untranslatable *and* produced a candidate from it, the candidate wins and the
  claim is dropped.

  Taken over the candidates **as read**, not over the ones that survived.  A sentence the
  reader turned into something the KB already stores, or into something the critic refused,
  was still read — reporting it as untranslated would blame the reader for the winnowing,
  and coverage is a claim about the *document*, not about the batch.

  This is part of the default answer rather than something a caller asks for, which is the
  whole point of it."
  [segs candidates untranslated]
  (let [known  (set (map :index segs))
        hit    (into #{} (comp (map :segment) (filter known)) candidates)
        reason (into {} (for [{:keys [segment reason]} untranslated
                              :when (int? segment)]
                          [segment reason]))]
    {:segments (count segs)
     :covered (count (filter #(hit (:index %)) segs))
     :uncovered (vec (for [{:keys [index text span]} segs
                           :when (not (hit index))]
                       (cond-> {:index index :span span :text text}
                         (reason index) (assoc :reason (reason index)))))}))

;; ---- the order a reviewer should work in --------------------------------

(defn review-queue
  "The candidates in the order a reviewer should read them: **flagged first**, then least
  confident first, then document order.

  `flagged` is the set of entry indices something has a reservation about — a coined functor
  (`vaelii.impl.llm.inventory/coined`) or a shape `vaelii.impl.llm.correct` would rewrite.
  Both are failures the check chain admits *by design* and only a person can settle, so they
  sort to the top whatever the candidate claims about itself; confidence is the parser's own
  account of how much of the claim was reading and how much was guessing, and it breaks the
  tie — which is all a confidence is for here."
  [entries flagged]
  (let [flagged (set flagged)]
    (vec (for [[i e] (sort-by (fn [[i e]]
                                [(if (flagged i) 0 1)
                                 (or (:confidence (entry-provenance e)) 1.0)
                                 (or (:segment (entry-provenance e)) Long/MAX_VALUE)
                                 i])
                              (map-indexed vector entries))]
           {:index i
            :entry e
            :flagged? (contains? flagged i)
            :confidence (:confidence (entry-provenance e))
            :segment (:segment (entry-provenance e))}))))
