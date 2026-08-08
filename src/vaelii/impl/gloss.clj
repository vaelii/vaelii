;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.gloss
  "A sentence in English, **composed** from what the KB already says about its own
  vocabulary rather than generated.

  The read path is the one with no verifier.  Nothing in the engine can say that an
  English sentence describing `(genl penguin bird)` is wrong, so a fluent gloss is a way
  to teach a reader something false through their only window onto the formal content —
  which makes reading the more dangerous direction here, not the safer one.  The defence
  is to not write prose at all where the KB has already written it.

  ## The comment is the template

  The vocabulary documents itself: every shipped predicate carries a `comment` sentex,
  and those comments are written in a shape that is already a template —

      (comment eats \"(eats ?animal ?food) means that ?animal takes ?food as nourishment. …\")
      (comment genl \"(genl ?subtype ?supertype) means that every ?subtype is a ?supertype. …\")

  a **signature** naming the argument positions with variables, then a clause saying what
  the predicate means *in those names*.  So glossing `(eats Muffet kibble)` is not a
  generation problem: read `eats`'s comment, take its first clause, substitute the actual
  arguments for the signature's variables.

  The variables are why it reads: a parameter spelled `?animal` cannot be mistaken for an
  individual the way `Animal` can, and because the *name* carries the sort, the clause
  after it needs no sortal noun to lean on — so what substitutes is the sentence a reader
  wants rather than one with `place Paris` in it.  Everything past that first clause is
  documentation for a reader, not template: how the predicate is used, what it is not,
  and what the KB does with it.

  A signature written with plain capitalized words and a colon — `(eats Animal Food):
  Animal eats Food` — is read the same way, since an imported vocabulary spells its own
  comments and they are not ours to rewrite.

  This is why the composer is a lookup and a substitution rather than a table of
  hand-written patterns: adding a predicate with a documented signature gives it a gloss
  for free, and a comment edited to say something else changes the gloss with it.  Of the
  277 shipped comments, 175 carry a signature; the 102 that do not are nouns — 86 types
  and 16 unit individuals — which need none, because a type gloss is \"X is a dog\" and
  the comment is the apposition after it.

  What the composition rate does **not** measure is whether a gloss is worth reading.  It
  earns its place where the predicate name is opaque — `genl` glossed as \"Every dog is an
  animal\" teaches a reader what `genl` means — and adds nothing where the predicate is
  already an English verb.

  ## What it will not do

  A term with no comment **degrades to naming the term**.  It does not invent a
  description, because an invented description is exactly the failure this exists to
  prevent, and a reader who sees the bare name has lost nothing they were entitled to.
  Every result carries `:source` saying which it got:

    :composed   every literal came from a comment
    :partial    some did; the rest are named
    :named      nothing to compose from — the terms, in a frame
    :generated  a model wrote it (`gloss` never does this; see `with-model`)

  The formal sentence is never replaced by the gloss — that is the caller's contract, and
  `docs/web.md` states it for the browser."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.core :as v]))

;; ---- reading a comment as a template -------------------------------------

(def ^:private long-clause
  "Past this many characters a clause is worth cutting at its em dash as well as at its
  sentence end.  Cutting at the dash first would truncate mid-thought — \"every (P ...)\"
  out of \"every (P ...) is deduced into UniverseContext — …\" — so the dash is the
  second cut and only for a clause that is already too long to read."
  140)

(defn- first-clause
  "The first readable clause of a comment: up to the first sentence boundary, the first
  parenthetical doc reference, or — only when what is left is still long — the first em
  dash.  Trailing punctuation goes with it.

  A sentence opens with a capital, an open paren, or a **variable**: a clause whose next
  sentence begins `?year is a plain number…` has ended just as surely as one whose next
  sentence begins `The year…`, and reading the parameter as mid-sentence would run the
  whole comment into the gloss."
  [s]
  (let [s   (str/trim s)
        cut (fn [text res]
              (let [ms (keep #(when-let [m (re-find % text)] (str/index-of text m)) res)]
                (if (seq ms) (subs text 0 (apply min ms)) text)))
        one (cut s [#"\. [A-Z(?]" #" \(docs/" #"\n"])
        one (if (> (count one) long-clause) (cut one [#" — " #" – "]) one)]
    (str/replace (str/trim one) #"[.,;:]+$" "")))

(def ^:private signature
  "A comment's head: a functor, its parameters, and the connector that ends it.

  Two connectors, because two vocabularies write them.  Ours reads `(genl ?subtype
  ?supertype) means that …` — variables for the positions, and a verb saying the clause
  is a definition.  `that` is optional so a *function* can be documented in the same
  shape without the grammar fighting it: `(QuantityFn ?magnitude ?unit) means the measure
  …` denotes a term rather than claiming a sentence.  An imported vocabulary reads
  `(genl Sub Super): …`, the same signature spelled without either, and is not ours to
  rewrite."
  #"^\([a-zA-Z_/][^\s()]*((?: [?a-zA-Z_][^\s()]*)*)\)(?::|\s+means(?:\s+that)?)\s*(.*)$")

(defn template
  "A comment read as a template: `{:params [\"?subtype\" \"?supertype\"] :text \"every
  ?subtype is a ?supertype\"}`, or `{:text …}` alone when the comment describes rather
  than parameterizes.

  A signature's parameters must be plain words or variables.  `(totalDuration (list I1 I2
  …) D)` names a compound argument, and substituting into it would need to know that
  `(list …)` is one argument rather than three — so it is read as a description instead,
  which loses the substitution and keeps the honesty."
  [text]
  (let [text (str/trim (str text))]
    (if-let [[_ params body] (re-find signature text)]
      {:params (vec (remove str/blank? (str/split (str/trim params) #"\s+")))
       :text   (first-clause body)}
      ;; a signature this cannot parse still should not be read *as prose*, since its
      ;; head is a formal sentence — strip it and keep the description after it
      (if-let [[_ body] (re-find #"^\([^\n]*?\)(?::|\s+means(?:\s+that)?)\s*(.*)$" text)]
        {:text (first-clause body)}
        {:text (first-clause text)}))))

(defn- comment-template
  "The template for `term`, or nil when the KB says nothing about it."
  [kb term]
  (when-let [text (first (v/sentexes-matching kb (list 'comment term '?text) '?ctx))]
    (template (nth (:sentence text) 2 nil))))

;; ---- rendering a term ----------------------------------------------------

(defn term-words
  "A term as it reads in prose.  A snake_case type is **de-spelled** — underscores become
  spaces — because `physical_object` is one word written with a typographic convention
  and not a description of anything; nothing else is touched, and a variable reads as its
  own letter.  The formal sentence sits beside every gloss, so a reader who wants the
  symbol has it."
  [t]
  (cond
    (and (symbol? t) (str/starts-with? (name t) "?")) (subs (name t) 1)
    (symbol? t)                                       (str/replace (name t) "_" " ")
    (string? t)                                       (str \" t \")
    :else                                             (pr-str t)))

(defn- articles
  "`a` before a vowel becomes `an`.  The article is the *comment's* — \"every SubType is a
  SuperType\" — and substitution is what puts a vowel after it, so repairing it is
  finishing the comment's own sentence rather than writing one.  `u` is left alone: a
  unaryPredicate, a unit."
  [s]
  (str/replace s #"(?i)\ba (?=[aeio])" #(if (= \A (first %1)) "An " "an ")))

(defn- drop-articles
  "The article a clause put before a *common noun* has to go when the noun becomes a
  name.  A clause reading `the ?animal can fly` is written about a kind, so substituting
  `Pingu` leaves \"the Pingu can fly\" — the comment's grammar, applied to an argument it
  did not anticipate.  An individual and a variable both take no article; a type still
  does, so `the dog can fly` is left exactly as the comment wrote it."
  [s params args]
  (reduce (fn [s a]
            (let [w (term-words a)]
              (if (or (and (symbol? a) (str/starts-with? (name a) "?"))
                      (and (symbol? a) (Character/isUpperCase ^char (first (name a)))))
                (str/replace s (re-pattern (str "(?i)\\b(?:the|an?) "
                                                (java.util.regex.Pattern/quote w) "\\b"))
                             (java.util.regex.Matcher/quoteReplacement w))
                s)))
          s (take (count params) args)))

(defn- replace-params
  "The clause with each parameter replaced by the argument in its position, and **how many
  were actually replaced**.

  The count is the point.  A comment is prose, and its clause may not use the parameter
  names its signature declares — `(disjoint ?type1 ?type2) means that the two types have
  no common instance` names neither, and an imported `(flies Animal): the animal can fly`
  names its own in the wrong case.  Substituting into either yields a fluent sentence that
  has silently lost the arguments, which is worse than not glossing at all: it reads as a
  claim about nothing in particular.  So the caller is told, and decides.

  Longest parameter first, so `A` cannot eat the `A` inside `Animal`.  The boundary is
  written out rather than left to `\\b`, because `?` is not a word character and `\\b?food`
  would match nothing at all.  A failed exact pass retries case-insensitively for
  parameters of more than two characters — enough to catch `Animal`/`animal`, not enough
  to let a parameter named `A` match the article."
  [{:keys [params text]} args]
  (let [pairs (sort-by (comp - count first) (map vector params args))
        pass  (fn [s ci?]
                (reduce (fn [[s n] [p a]]
                          (let [re (re-pattern (str (when ci? "(?i)") "(?<![\\w?])"
                                                    (java.util.regex.Pattern/quote p)
                                                    "(?!\\w)"))]
                            (if (re-find re s)
                              [(str/replace s re (java.util.regex.Matcher/quoteReplacement
                                                  (term-words a)))
                               (inc n)]
                              [s n])))
                        [s 0]
                        (if ci? (filter #(> (count (first %)) 2) pairs) pairs)))
        [s n] (pass text false)
        [s n] (if (pos? n) [s n] (pass text true))]
    [(articles (drop-articles s params args)) n]))

;; ---- glossing one literal ------------------------------------------------

(defn- and-list
  "Arguments as a reader would say them: *dog and cat*, *a, b and c*."
  [ws]
  (case (count ws)
    0 ""
    1 (first ws)
    (str (str/join ", " (butlast ws)) " and " (last ws))))

(defn- type-literal
  "A unary literal whose predicate declares no signature is a type membership, and reads
  as one: *Muffet is a dog*, with the type's own comment as the apposition after it.  This
  is where the signature-less comments earn their place — a noun phrase is exactly what
  belongs after \"is a\".

  `apposition?` is false wherever the gloss is nested — inside a rule or a negation —
  because a clause carrying a dashed definition of each of its terms stops being a
  sentence anyone can read."
  [kb [pred arg] apposition?]
  (let [t    (comment-template kb pred)
        head (articles (str (term-words arg) " is a " (term-words pred)))
        d    (some-> t :text str/trim not-empty)]
    (cond
      (and d apposition?) {:text   (str head " — " (str/lower-case (subs d 0 1)) (subs d 1))
                           :source :composed}
      d                   {:text head :source :composed}
      :else               {:text head :source :named})))

(defn- relation-literal
  "A literal glossed by substituting its arguments into its predicate's signature.

  Three outcomes, and the middle one is the reason `replace-params` counts.  A signature
  whose clause actually names its parameters composes.  A signature whose clause names
  none of them — `(disjoint ?type1 ?type2) means that the two types have no common
  instance` — would otherwise render a true sentence about unnamed things, so the
  arguments are said and the clause follows them as a description; that is `:partial`,
  because half of it is a name rather than a description.  No usable signature at all is
  named outright."
  [kb [pred & args]]
  (let [t (comment-template kb pred)
        clause (some-> t :text str/trim not-empty)]
    (if (and t clause (= (count (:params t)) (count args)))
      (let [[text n] (replace-params t args)]
        (if (pos? n)
          {:text text :source :composed}
          {:text (str (and-list (map term-words args)) ": " clause) :source :partial}))
      (if clause
        {:text (str (and-list (map term-words args)) ": " clause) :source :partial}
        {:text (str (term-words pred) ": " (str/join ", " (map term-words args)))
         :source :named}))))

(defn- literal
  "One atomic literal, or a negation of one.

  A **unary** literal is routed by the predicate's own comment rather than by its
  spelling: a signature of one parameter means the comment already says how to phrase it
  (`(flies ?animal) means that ?animal can fly`), and no signature means the comment is a
  noun phrase and the literal is a type membership.  Spelling cannot decide this — a bare
  lowercase word satisfies the type convention and the predicate convention alike."
  ([kb sent] (literal kb sent true))
  ([kb sent apposition?]
   (cond
     (not (sequential? sent))
     {:text (term-words sent) :source :named}

     (and (= 'not (first sent)) (sequential? (second sent)))
     (let [{:keys [text source]} (literal kb (second sent) false)]
       {:text (str "it is not true that " text) :source source})

     (and (= 2 (count sent))
          (not= 1 (count (:params (comment-template kb (first sent))))))
     (type-literal kb sent apposition?)

     :else (relation-literal kb sent))))

;; ---- glossing a sentence -------------------------------------------------

(defn- conjuncts
  "The literals of an `(and …)` frame, or the one literal that is not one."
  [s]
  (if (and (sequential? s) (= 'and (first s))) (rest s) [s]))

(defn- worst
  "A sentence's source is the weakest of its parts': one named literal makes the whole
  thing partial, and a gloss that is entirely named says so."
  [sources]
  (let [ss (set sources)]
    (cond
      (= ss #{:composed}) :composed
      (= ss #{:named})    :named
      :else               :partial)))

(defn- sentence-case
  "A capital and a full stop — **unless the line opens with a term**, in which case the
  capital is left alone.  Upper-casing `siblingOf` into `SiblingOf` does not tidy a
  sentence, it renames a predicate into something that reads as an individual, and the
  one thing a gloss may never do is misspell the vocabulary it is glossing."
  [s opens-with-term?]
  (cond
    (str/blank? s)   s
    opens-with-term? (str s ".")
    :else            (str (str/upper-case (subs s 0 1)) (subs s 1) ".")))

(defn- rule
  "A rule reads as the conditional it is: *If x is a bird, then x flies.*  The antecedent
  and consequent are glossed as literals, so a rule costs no machinery of its own — and
  they are glossed **without appositions**, since a conditional whose every term drags a
  dashed definition behind it is not a sentence."
  [kb {:keys [antecedent consequent]}]
  (let [ants (map #(literal kb % false) antecedent)
        con  (literal kb consequent false)]
    {:text   (str "If " (str/join ", and " (map :text ants)) ", then " (:text con))
     :source (worst (map :source (cons con ants)))}))

(defn gloss
  "`sentence` in English, composed from the KB's own comments.  **Never calls a model** —
  the answer is a lookup and a substitution, so a sentence over documented vocabulary
  costs zero model calls by construction rather than by luck.

  Answers `{:text :source}`; `:source` is `:composed` / `:partial` / `:named` as described
  in the namespace docstring.  A caller must render the formal sentence alongside."
  [kb sentence]
  (cond
    (nil? sentence) {:text "" :source :named}

    ;; a rule arrives either as a record (`:antecedent` is the discriminant) or as the
    ;; `implies` form a caller has in hand before anything is stored
    (and (map? sentence) (:antecedent sentence))
    (rule kb sentence)

    (and (sequential? sentence) (= 'implies (first sentence)))
    (rule kb {:antecedent (conjuncts (second sentence)) :consequent (nth sentence 2 nil)})

    :else (literal kb sentence)))

(defn readable
  "The gloss of a stored sentex, with its sentence read back in the author's own variable
  names — the shape a reader recognizes, rather than the canonical `?var0` the store
  keeps."
  [kb sx]
  (gloss kb (if (:antecedent sx)
              {:antecedent (conjuncts (second (v/readable-sentence sx)))
               :consequent (nth (v/readable-sentence sx) 2 nil)}
              (v/readable-sentence sx))))

(defn- terms-of
  "Every symbol in a sentence, as it would be rendered — what `sentence-case` checks the
  line against before capitalizing it."
  [s]
  (into #{} (comp (filter symbol?) (map term-words)) (tree-seq sequential? seq s)))

(defn text
  "The gloss as one sentence-cased line, which is what a page renders."
  [kb sentence]
  (let [g (gloss kb sentence)
        opens (some #(str/starts-with? (:text g) %) (terms-of sentence))]
    (update g :text sentence-case (boolean opens))))

;; ---- the model, only where composition ran out ---------------------------

(defn with-model
  "`gloss`, falling back to `ask` for a sentence the KB documents nothing about.

  Deliberately a separate entry point rather than a branch inside `gloss`: the guarantee
  worth having is that the ordinary path cannot reach a model at all, and a guarantee
  that depends on an argument being nil is not one.  The fallback fires only on `:named`
  — a partially composed gloss keeps what the KB actually said rather than handing the
  whole sentence to a model that would rewrite the documented half too.

  The result is marked `:generated`, and a caller must render that distinctly: the reader
  is entitled to know which they are reading."
  [kb sentence ask]
  (let [g (text kb sentence)]
    (if (and ask (= :named (:source g)))
      ;; A model failure logs before it degrades. Swallowing it made a bad key, a
      ;; 429, a timeout and "the model returned whitespace" indistinguishable from
      ;; each other and from "this sentence has a named gloss already" — so a reader
      ;; who wires up a provider and sees no generated text has nothing to look at.
      (if-let [said (try (some-> (ask sentence) str str/trim not-empty)
                         (catch Exception e
                           (trove/log! {:level :warn :id ::gloss-failed :error e
                                        :msg "gloss generation failed; using the composed text"
                                        :data {:sentence sentence}})
                           nil))]
        {:text (sentence-case (first-clause said) false) :source :generated}
        g)
      g)))
