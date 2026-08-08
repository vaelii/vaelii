;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.naming
  "KB naming invariants, as predicates over symbols — and the walk that applies them to
  every **literal** of a sentence rather than to its outermost functor alone.

    predicate    camelCase, lowercase-initial, no underscore   parentOf, genl, argIsa
    individual   CapitalCamelCase                               Muffet, Tom
    type         snake_case, lowercase, unary predicate         dog, physical_object
    sense        a type, plus which sense of it is meant        abrasive-grit
    context      CapitalCamelCase ending in Context             UniverseContext, CoreContext
    lexeme       the `lex` namespace; the name is parse input   lex/fool's_gold

  Single lowercase words (dog, genl, parentOf) satisfy both `predicate?` and
  `type-symbol?`; role is disambiguated by position and arity, not the symbol alone.
  A sense is a type too, so it is unary for the same reason, and a lexeme is the one
  role a *namespace* decides — its text is a surface form and not ours to spell.
  A functor carrying an **underscore** is a type name and nothing else, and types are
  used as *unary* predicates — `(dog Muffet)`, not `(isa Muffet Dog)` — so it is legal at
  arity 1 and nowhere else.  `(lives_in penguin cold_place)` is a type name doing a
  relation's job; admitting it fragments the vocabulary into one-off predicates
  (`lives_in_antarctica`, `capable_of_swimming`) that can never join a rule or match
  another sentence.

  How hard these are enforced is the **KB's** to say, not this namespace's: `open-kb`'s
  `:naming` selects `:strict` / `:warn` / `:off` (`policies`, below) and `assert` reads
  it.  The predicates themselves do not move — `:off` stores a name nothing can classify,
  not one classified differently.

  `problems` checks the functor of every literal a sentence contains — a rule's
  antecedents, its consequent, an `exceptWhen` query's conjuncts, a `not` body, an
  `ist`-directed sentence, a negation-as-failure query — not only the outermost one.
  A rule consequent is exactly where generated content lands, and the outermost
  functor there is `implies`."
  (:refer-clojure :exclude [name])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.sentex :as sx]))

(defn- nm [s] (clojure.core/name s))

(def lexeme-namespace
  "The namespace marking a **lexeme** — a surface form exactly as a model or a person
  wrote it, before anything decided what it means.  A namespace rather than a spelling
  because a lexeme's own text is unconstrained: it carries apostrophes (`fool's_gold`),
  dashes, dots and digits, so any marker written *into* the name would collide with the
  word it marks.  `(namespace x)` is a field read and cannot."
  "lex")

(defn lexeme?
  "A lexeme: `lex/fool's_gold`.  Parse input, and the only role whose text this makes no
  claim about — what a person typed is not ours to spell.

  Every other namespace stays invisible to the role checks, exactly as before: `nm` reads
  the name half, so `agg/count` and `set/forwardRule` are the predicates they always
  were.  `lex` is the one namespace that decides a role."
  [x]
  (and (symbol? x) (= lexeme-namespace (namespace x))))

(defn context?    [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[A-Z][A-Za-z0-9]*Context" (nm x)))))
(defn individual? [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[A-Z][A-Za-z0-9]*" (nm x)))
                           (not (context? x))))
(defn predicate?  [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[a-z][a-zA-Z0-9]*" (nm x)))))

(def ^:private disambiguator-re
  "A **sense** — a word, a `-`, and the disambiguator that says which sense of it is
  meant: `abrasive-grit`, `abandonment-romantic`, `abandonment-dual`.  Senses are the
  type hierarchy, and the disambiguator is what makes two senses of one word two terms
  rather than one.

  The split is on the **last** dash, because the word may hold its own — and may *end*
  in one, which is the case that forces the rule.  `a-` is a word (A, then the minus),
  so its sense is `a--musical_note`: the word is `a-`, the disambiguator is
  `musical_note`, and the boundary is the second dash rather than the first.  Nothing
  here parses that boundary — the `sense` and `disambiguation` facts record it, and this
  only has to recognise the shape.

  Both halves admit what real vocabulary carries — a leading dot (`.22_long_rifle-ammo`,
  `.dll-library`), an internal apostrophe (`fool's_gold-mineral`, `deck-ship's_floor`), a
  dash of the word's own, and a disambiguator that starts with a digit (`organ_cultures-3d`,
  `chiptune_composer-8bit`).  A disambiguator is minted rather than found, so it is
  tempting to hold it to snake_case — but the corpus mints `3d` and `8bit`, and they are
  good disambiguators.  Only the **first character of the whole symbol** is constrained,
  because only it is what the reader dispatches on.

  What it may not do is **lead with a digit**, and the reason is the reader rather than
  taste: `134a-gas` is read as a malformed *number*, not as a symbol, so a KB holding one
  could not be written to text and read back.  A leading `'`, `#` or `:` fails the same
  way.  A word that starts with a digit is escaped with an underscore when it is minted
  — `_134a-gas` — which reads, sorts beside its neighbours, and says it was escaped."
  #"[a-z._][a-z0-9_'.+=&:*>#-]*-[a-z0-9][a-z0-9_']*")

(defn sense?
  "A disambiguated type."
  [x]
  (and (symbol? x) (not (lexeme? x))
       (some? (re-matches disambiguator-re (nm x)))))

(defn type-symbol?
  "A type: bare snake_case (`dog`, `physical_object`) or a sense (`abrasive-grit`).
  Both are unary predicates — a sense is a type that says which sense it is."
  [x]
  (and (symbol? x) (not (lexeme? x))
       (or (some? (re-matches #"[a-z][a-z0-9_]*" (nm x)))
           (sense? x))))

(defn functor [sentence] (when (sequential? sentence) (first sentence)))
(defn args    [sentence] (when (sequential? sentence) (rest sentence)))
(defn arity   [sentence] (if (sequential? sentence) (dec (count sentence)) 0))

;; ---- the literals of a sentence ------------------------------------------
;; A naming invariant is about a **literal** — a predicate applied to arguments.
;; Everything else a sentence is built from is a *frame*: a structural connective
;; (`not` / `and` / `implies`), a virtual rule wrapper (`set/*Rule`), an `exceptWhen`,
;; an `ist` redirection, a negation-as-failure quantifier, a `sentexHandle` naming
;; another sentex.  A frame's functor is engine vocabulary rather than a name the
;; author chose, so the walk descends through it and checks what it holds.
;;
;; Arguments are deliberately **not** walked: a compound in argument position is a
;; term, not a literal — an arithmetic expression `(+ 1 2)`, a structural NAT `(QuantityFn 5
;; Meter)`, a quoted connective `(comment not "…")` — and its head names a function or
;; is plain data, neither of which the predicate conventions govern.

(def ^:private literal-roles
  "The frame a literal sits in, as it reads in a rejection.  A repair loop is handed
  the message verbatim, so it has to say *which* literal of the sentence broke."
  {:sentence   "sentence"
   :antecedent "rule antecedent"
   :consequent "rule consequent"
   :exception  "exceptWhen exception"})

(def problem-classes
  "What a naming violation *is*, as a keyword, with the human line under it.  A rejection
  reads as prose, but a caller that counts them needs to group without parsing English —
  an operator auditing a corpus wants five numbers, not eleven million sentences — so the
  class is the datum and the message is rendered from it."
  {:context-name   "the KB context named is not a context"
   :functor        "a functor matching no convention"
   :functor-arity  "a snake_case functor (a type) at an arity other than 1"
   :lexeme-functor "a lexeme applied to arguments — a surface form names no relation"
   :argument       "a symbol argument matching no convention"
   :ist-context    "an ist context slot that does not name a context"
   :dot-marker     "a dotted rest marker outside a rule pattern"})

(defn- rule-wrapper?
  "One of the virtual wrappers that wrap a single rule form — direction, defeasible,
  assumption, constraint.  Each canonicalizes into a record field, so none of them is
  ever a predicate application."
  [h]
  (or (contains? sx/rule-direction-wrappers h)
      (= sx/default-rule-wrapper h)
      (= sx/assumption-rule-wrapper h)
      (contains? sx/constraint-rule-wrappers h)))

(defn- exception-query-conjuncts
  "The conjunct literals of an `exceptWhen` wrapper's query: a vector is a conjunction,
  anything else a single literal.  The shape `sentex/exception-conjuncts` normalizes,
  read here without canonicalizing — a check must not intern the symbols of content it
  is about to refuse."
  [q]
  (if (vector? q) q [q]))

(defn applied-literals
  "The `[role literal]` pairs of `sentence` as written — every position at which it
  applies *something* to arguments, tagged with the frame that position sits in
  (`:sentence` / `:antecedent` / `:consequent` / `:exception`).

  Frames are descended through, arguments are not, so this is exactly the set of
  positions an author wrote a predicate application in — a variable functor
  (`(?p ?x ?y)`, the dotted rest `(?pred . ?args)`) among them, which is what
  `literals` filters back out and `rules/variable-functor-literals` keeps."
  ([sentence] (applied-literals :sentence sentence))
  ([role form]
   (if-not (and (sequential? form) (seq form))
     []
     (let [h (first form)
           n (count form)]
       (cond
         ;; a `do/` imperative is an instruction; it is refused outright inside a rule
         ;; (`core/check-no-imperative`) and dispatched at the top level, never named
         (sx/do-form? form) []

         ;; `(sentexHandle N)` names a stored sentex by integer id
         (= sx/sentex-handle-functor h) []

         (sx/variable? h) [[role form]]

         (rule-wrapper? h) (applied-literals role (second form))

         ;; `(exceptWhen <query> <rule-or-handle>)` — the query's conjuncts are
         ;; literals of their own, then whatever the exception qualifies
         (and (= sx/except-wrapper h) (= 3 n))
         (into (vec (mapcat #(applied-literals :exception %)
                            (exception-query-conjuncts (second form))))
               (applied-literals role (nth form 2)))

         (and (= sx/not-functor h) (= 2 n)) (applied-literals role (second form))

         (= sx/and-functor h) (vec (mapcat #(applied-literals role %) (rest form)))

         (and (= sx/rule-functor h) (= 3 n))
         (into (vec (mapcat #(applied-literals :antecedent %) (sx/rule-antecedents form)))
               (applied-literals :consequent (sx/rule-consequent form)))

         ;; `(ist Ctx S)` directs S into Ctx; S is the literal (Ctx is checked by
         ;; `ist-context-problems`)
         (and (= sx/ist-functor h) (= 3 n)) (applied-literals role (nth form 2))

         ;; negation as failure: `(unknown S)` and `(thereExists <vars> S)` frame a
         ;; query, and a head `(exists <vars> C)` frames the consequent it quantifies
         (sx/unknown? form)      (applied-literals role (second form))
         (sx/there-exists? form) (applied-literals role (nth form 2))
         (sx/head-exists? form)  (applied-literals role (sx/head-exists-body form))

         ;; an aggregate frames a query too: `(agg/count ?n ?v <body>)` says
         ;; nothing itself, and its body is a goal rather than an argument — read as a
         ;; literal it would be a three-place `agg/count` and the body inside it
         ;; would never be checked at all
         (sx/aggregate? form)    (applied-literals role (sx/aggregate-body form))

         :else [[role form]])))))

(defn literals
  "The `[role literal]` pairs whose functor **names a predicate** — `applied-literals`
  without the variable-functor positions, which are patterns and name nothing these
  invariants can judge.  This is the set of functors an author named, and what every
  check below reads."
  ([sentence] (literals :sentence sentence))
  ([role form]
   (filterv (fn [[_ lit]] (not (sx/variable? (first lit))))
            (applied-literals role form))))

;; ---- the invariants, per literal -----------------------------------------

(defn- camel-case
  "The camelCase spelling of a snake_case symbol — `lives_in` ⇒ `livesIn`.  Named in
  the rejection so whoever reads it is told what to write, not only what is wrong."
  [s]
  (let [[head & more] (str/split (nm s) #"_+")]
    (apply str head (map str/capitalize more))))

(defn- functor-problem
  "The naming violation of one `[role literal]` pair's functor, or nil.  Two ways to
  fail: the symbol matches no convention at all, or it is snake_case — a type name —
  used at an arity other than 1."
  [[role literal]]
  (let [f (functor literal)]
    (cond
      (nil? f) nil

      ;; The one fence around a lexeme, and the whole of it.  A surface form is what
      ;; somebody wrote, not a relation or a kind, so it cannot be applied to anything —
      ;; while as an *argument* it is ordinary, which is what lets `(sense lex/w s)` say
      ;; what a lexeme means and `(genl s lex/w)` stand as the improver's unsensified
      ;; edge until it crafts the sense that replaces it.
      (lexeme? f)
      {:class :lexeme-functor :role role :symbol f :literal literal}

      (not (or (predicate? f) (type-symbol? f)))
      {:class :functor :role role :symbol f :literal literal}

      (and (not (predicate? f)) (not= 1 (arity literal)))
      {:class :functor-arity :role role :symbol f :literal literal})))

(defn- pascal-case
  "The CapitalCamelCase spelling of an underscored symbol — `South_Pole` ⇒ `SouthPole`."
  [s]
  (apply str (map str/capitalize (str/split (nm s) #"_+"))))

(defn- argument-problem
  "The naming violation of one atomic symbol argument, or nil.  An argument *names*
  something — an individual, a type, a predicate, a context — so it is held to the
  same conventions as a functor.  `Baby_Penguin` matches none of them: CapitalCamelCase
  admits no underscore and snake_case no capital, so the symbol claims two roles and
  fills neither.  Both repairs are named, since which one is meant is the author's to
  say: `BabyPenguin` if it is an individual, `baby_penguin` if it is a type.

  Only the literal's **own** arguments are checked, never a compound one's insides: a
  compound in argument position is a term — `(+ 1 2)`, a structural NAT `(QuantityFn 5 Meter)` —
  and its head is a function, not a name this can judge.  Non-symbols (a number, a
  comment's string) name nothing and are skipped, as is a variable and the dotted rest
  marker."
  [[role literal] a]
  (when (and (symbol? a)
             (not (sx/variable? a))
             (not= sx/dot-marker a)
             (not (or (individual? a) (context? a) (predicate? a) (type-symbol? a)
                      (lexeme? a))))
    {:class :argument :role role :symbol a :literal literal}))

(defn- ist-context-problems
  "The `(ist Ctx S)` context slots that do not name a context.  A rule consequent
  `(ist Ctx S)` places S into Ctx, so that slot is a context name like the asserting
  context — or a variable an antecedent binds, which is resolved at firing time."
  [sentence]
  (for [f (tree-seq sequential? seq sentence)
        :when (and (sequential? f) (= sx/ist-functor (first f)) (= 3 (count f)))
        :let [c (second f)]
        :when (not (or (sx/variable? c) (context? c)))]
    {:class :ist-context :role :sentence :symbol c :literal f}))

(defn message
  "One `problems*` map rendered as the line a rejection carries.  Every message names
  the offending symbol, the frame it sits in and the spelling to write instead: whoever
  reads it is mid-repair, and a violation reported without its fix is a second lookup."
  [{:keys [class role symbol literal]}]
  (let [where (str (literal-roles role) " " (pr-str literal))]
    (case class
      :context-name
      (str "context " symbol " must be CapitalCamelCase ending in Context")

      :functor
      (str "functor " (pr-str symbol) " in " where " matches no naming convention: a"
           " predicate is camelCase (parentOf, argIsa), a type is snake_case"
           " (physical_object) or a sense (abrasive-grit), and a type is only unary")

      :lexeme-functor
      (str "functor " (pr-str symbol) " in " where " is a lexeme, and a surface form names"
           " no relation, so it cannot be applied to anything — write the sense it means,"
           " " (nm symbol) "-<which sense>, or leave it in argument position, where"
           " (sense " symbol " <the sense>) says what it means")

      :functor-arity
      (if (sense? symbol)
        (str "functor " symbol " in " where " is a sense, which names a type and is legal"
             " only as a unary predicate, but has " (arity literal) " arguments — write the"
             " relation as a camelCase predicate, or as (" symbol " <one argument>)")
        (str "functor " symbol " in " where " is snake_case, which names a type and is legal"
             " only as a unary predicate, but has " (arity literal) " arguments — write it"
             " camelCase as " (camel-case symbol) ", or as (" symbol " <one argument>)"))

      :argument
      (str "argument " (pr-str symbol) " in " where
           " matches no naming convention: an individual is CapitalCamelCase (Muffet), a"
           " type is snake_case (physical_object) or a sense (abrasive-grit), and a"
           " predicate is camelCase (parentOf) — write it " (pascal-case symbol)
           " for an individual, or " (str/lower-case (nm symbol)) " for a type")

      :ist-context
      (str "ist directs " (pr-str literal) " into " (pr-str symbol)
           ", which must be CapitalCamelCase ending in Context, or a variable an"
           " antecedent binds")

      :dot-marker
      "'.' is not a valid argument (dotted rest patterns belong in rule patterns)")))

(defn problems*
  "Checkable naming violations for a sentence in a context, as **data**: a vector of
  `{:class :role :symbol :literal}` maps in the order `problems` reports them.  `:class`
  is one of `problem-classes`, `:role` the frame the offending literal sits in, `:symbol`
  the name that broke the convention, and `message` renders the line.

  Data rather than prose because the two callers want different halves of it.  `assert`
  wants the sentence it refused spelled out; an audit over a whole corpus wants to
  *group* — how many violations, of which class, over how many distinct spellings — and
  a message that embeds the literal is unique per record, so counting them counts
  records.  Rendering is therefore separate and paid only where a message is read."
  [sentence context]
  (into []
        cat
        [(when-not (context? context)
           [{:class :context-name :role :sentence :symbol context :literal nil}])
         (keep functor-problem (literals sentence))
         (for [pair (literals sentence)
               a    (args (second pair))
               :let [p (argument-problem pair a)]
               :when p]
           p)
         (ist-context-problems sentence)
         ;; a bare `.` is the dotted rest-pattern marker; it belongs inside a rule
         ;; antecedent, never as a top-level argument of an asserted sentence.
         (when (some #(= sx/dot-marker %) (args sentence))
           [{:class :dot-marker :role :sentence :symbol sx/dot-marker :literal sentence}])]))

(defn problems
  "Checkable naming violations for a sentence in a context (seq of strings): the
  context's own name, then every literal's functor (outermost frame first), then every
  literal's atomic symbol arguments, then any `ist` context slot, then the dotted rest
  marker where it cannot appear.

  **This is a check on the shape of a name, not on whether the name is worth having.**
  A *unary* snake_case functor is a well-formed type name, so
  `(implies (penguin ?x) (has_black_and_white_feathers ?x))` passes here, and so would
  `capable_of_swimming` or `thermoregulates_via_blubber_and_feathers` — each is exactly
  what the invariants say a type looks like.  Nothing about a symbol distinguishes a
  type the ontology wants from a one-off coined for a single sentence, so nothing here
  can refuse the second: judging that needs the KB's existing vocabulary, which is a
  separate question asked elsewhere.  Read this as a guard against *misnamed* content,
  never as a guard against vocabulary fragmentation."
  [sentence context]
  (mapv message (problems* sentence context)))

;; ---- the policy: whose invariants, and how hard ---------------------------
;;
;; The conventions above are what *this* KB reads a role off, and a KB holding a corpus
;; that spells its names differently is not thereby malformed — it is a KB whose front
;; door is set to a different opinion.  So the policy is per-KB (`open-kb`'s `:naming`),
;; not a property of the build: one process can hold a strict KB beside a corpus loaded
;; verbatim, and neither has to win.
;;
;; What the setting does **not** change is the role reading.  `predicate?` and its three
;; siblings answer the same way under every policy, so `:off` is a KB that stores a name
;; it cannot classify — `term-role` says nil, a `(Type Individual)` goal takes the general
;; path rather than the shortcut — rather than one that classifies differently.  That is
;; the whole cost, and it is why the check is worth keeping on where the content is
;; hand-written.

(def policies
  "What a KB does with a naming violation, and the one line each is for.

  A bulk path is not on this list because it does not consult it: a corpus import builds
  records directly and never asks (`docs/naming.md`, \"The two doors\").  What it does
  instead is *report* — an operator learns the refused fraction at load time, from a
  count rather than from a failed experiment a year later."
  {:strict "refuse the assertion (the default: names stay legible)"
   :warn   "log each one and store anyway (a corpus being cleaned up)"
   :off    "store in silence (a corpus with its own spelling conventions)"})

(defn blocking-problems
  "The naming violations that **stop** something under `policy` — the messages, or nil.
  Empty under `:warn` and `:off` by construction, so a caller that has to yield a value
  rather than throw (`special/definitional-violation`, the `assert` dry run) asks this
  and needs no policy branch of its own."
  [policy sentence context]
  (when (= :strict policy) (seq (problems sentence context))))

;; ---- the other door: count what it would have refused ---------------------
;;
;; A bulk path stores what `assert` refuses, which is the point of having one — but a
;; store whose contents the front door disagrees with is a fact about that store, and the
;; only moment anybody is in a position to learn it cheaply is while the records are
;; going past.  So the bulk paths **count** what they do not check.  The tally is a
;; running map rather than a scan afterwards: a second pass over a corpus that needed a
;; bulk path in the first place is a second pass nobody will run.

(def empty-tally
  "A fresh `tally` accumulator: records seen, records with at least one violation, and
  the per-class breakdown.  Counts records rather than violations — one sentence can
  break three conventions, and what an operator is deciding is what fraction of the
  corpus is re-assertable."
  {:checked 0 :refused 0 :by-class {}})

(defn tally
  "Fold one sentence's violations into `t`.  Counts and classes only, never spellings: a
  corpus large enough to need a bulk path has a vocabulary large enough that holding its
  distinct offending names would cost more than the load
  (`vaelii.bench.survey`'s `naming` audit is where that question is asked)."
  [t sentence context]
  (let [ps (problems* sentence context)
        t  (update t :checked inc)]
    (if (empty? ps)
      t
      (-> t
          (update :refused inc)
          (update :by-class
                  #(reduce (fn [m c] (update m c (fnil inc 0)))
                           % (into #{} (map :class) ps)))))))

(defn tally-line
  "The one line a load prints about `t`, or nil when the front door agrees with the
  corpus — which is the common case and deserves no output at all."
  [t]
  (let [{:keys [checked refused by-class]} t]
    (when (pos? (long refused))
      (str (format "%,d of %,d records (%.1f%%) hold names `assert` would refuse: "
                   (long refused) (long checked)
                   (* 100.0 (/ (double refused) (double (max 1 checked)))))
           (str/join ", " (for [[c n] (sort-by val > by-class)]
                            (str (clojure.core/name c) " " (format "%,d" (long n)))))
           " — they are stored, findable and countable, but re-asserting one throws"
           " under :naming :strict"))))

;; Advice already given in this process, so a corpus of the same mistake is one line
;; rather than a line per fact.  `defonce` for the same reason the space counter is.
(defonce ^:private advised (atom #{}))

(defn- type-spelling
  "The type name a CapitalCamelCase symbol was reaching for: `Dog` is `dog`, and
  `PhysicalObject` is `physical_object` rather than `physicalobject` — types are
  snake_case, so lower-casing alone would suggest a name the conventions refuse."
  [s]
  (-> (nm s)
      (str/replace #"(?<=[a-z0-9])([A-Z])" "_$1")
      str/lower-case))

(defn advice
  "A well-formed sentence that is nonetheless almost certainly not what was meant — or
  nil.  Where `problems` reads the invariants, this reads *intent*, so everything here
  passes every check and stores cleanly.

  One entry so far.  `(isa Muffet Dog)` is the membership spelling every other KR system
  taught the reader, and here it stores a two-place predicate named `isa` relating two
  individuals — legal, indexed, believed, and matched by nothing anyone will ask.  The
  reader then asks `(isa? kb 'Muffet 'Dog)` and gets false, with no error to search for,
  because the type they meant was never asserted.  `CoreContext.txt` says never to write
  it and `docs/naming.md` calls it out by name; neither is in front of someone who is
  typing.

  The bar for a new entry is that the shape has no legitimate reading: `isa` is a
  predicate no shipped KB declares and the one the ontology names as the mistake.  A
  shape somebody might mean stays out — a nudge that fires on correct input is one that
  gets tuned out, and takes the real ones with it."
  [sentence]
  (let [f     (functor sentence)
        [x t] (vec (args sentence))]
    (when (and (= 'isa f) (= 2 (arity sentence)))
      {:id      ::isa-is-not-how-membership-is-written
       :message (str "(isa " x " " t ") stores a two-place `isa` predicate, which nothing "
                     "reads — types here are unary predicates, so membership is written "
                     ;; the rewrite only where both arguments are symbols: an argument
                     ;; may legally be a number, a string or a compound term, and
                     ;; `clojure.core/name` throws on all three — advice that crashes
                     ;; the assert it was meant to help is worse than none
                     (if (and (symbol? x) (symbol? t))
                       (str "(" (type-spelling t) " " x ")")
                       "as a unary type predicate, (dog Muffet)")
                     " and the hierarchy with genl.  docs/naming.md")})))

(defn advise!
  "Log `advice` about `sentence`, once per process per kind of advice.

  Silent under `:naming :off`, which asks for names not to be policed at all.  Never a
  refusal at any policy: the sentence is well-formed, and refusing a legal shape on a
  guess about intent would make the front door unpredictable."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [{:keys [id message]} (advice sentence)]
      (when-not (contains? @advised id)
        (swap! advised conj id)
        (trove/log! {:level :warn :id ::probably-not-meant
                     :msg  (str "stored, and probably not what was meant: " message)
                     :data {:sentence sentence :context context :advice id}})))))

(defn check!
  "Enforce `policy` on `sentence` in `context`: throw `:naming` under `:strict`, log
  under `:warn`, do nothing under `:off`.  The one place the three differ, so no caller
  spells the throw out and none can drift from another.

  Past the invariants it also gives `advice` — for a sentence that breaks none of them
  and is still a mistake, which a refusal cannot reach."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [ps (seq (problems sentence context))]
      (if (= :warn policy)
        (trove/log! {:level :warn :id ::naming-violation
                     :msg  (str "naming invariant (stored anyway, :naming :warn): "
                                (str/join "; " ps))
                     :data {:sentence sentence :context context}})
        (throw (ex-info (str "naming invariant: " (str/join "; " ps))
                        {:type :naming :sentence sentence :context context}))))
    (advise! policy sentence context)))
