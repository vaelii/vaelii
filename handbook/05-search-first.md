# 5. Search first

- **Covers:** searching every place a definition can live before minting a term, and what
  to do when the search finds a near match.
- **Not here:** the block a new term ships with → [ch. 6](06-definitional-block.md); the
  spelling that fixes a new term's role → [ch. 8](08-kind-of-term.md).
- **Assumes:** [ch. 4](04-economy.md) (**DRY**).

Minting a term takes one block of sentences, and merging two terms moves every sentence
stated with either. Nothing in vaelii stops a second name for a concept the KB already
has, and once facts and rules accumulate under both names the merge touches all of them.
The search before minting is the check the engine does not run.

## look before you mint

*Search everywhere before minting a term*

**genlPrinciple:** DRY

**Practice.** Before declaring a term new, search every place a definition can live:

- the shipped KB files, `resources/kb/upper/` and `resources/kb/middle/`, and every
  overlay or knowledge directory a deployment loads;
- setup and migration code, which may assert vocabulary of its own;
- the test fixtures, which show the intended use of a term even where no KB file states it;
- every branch, since a term may be proposed on one and not yet landed;
- the live KB a change will land in;
- the discussion history where vocabulary is proposed and declined.

Search by meaning as well as by name. A concept may be spelled with another word, as a
sense, or under a broader type whose comment names the case. A term "not found" in one
place is often defined in another.

**Example.** A change that wants an `artifact` type finds, in abstract.txt, that the KB
already divides tangibles by origin and names the artifact kinds by structure:

```clojure
(partition tangible made natural)
(genl machine mechanism)
(genl container made)
```

The search is a set of commands, each answering one of the places above:

```sh
git grep -nwE 'artifact|made|mechanism' -- resources/kb
git log --all --oneline -S 'artifact' -- resources/kb
git grep -nw 'artifact' -- test
```

Against the live KB, `describe` answers what the KB holds about a candidate name, and a
match over comments finds a concept by the words that define it:

```clojure
(v/describe kb 'made 'CxUniverse)
(v/ask kb '(comment ?term ?text) 'CxUniverse)
```

**Why.**

- **Logic.** Two names for one concept are two predicates. Nothing in the KB says they
  have the same extension, so a fact stated with one name is not a fact about the other.
- **Engine.** The naming check reads a symbol's spelling and nothing else. It checks how a
  name is spelled and is no guard against vocabulary fragmentation: a well-formed
  `snake_case` type passes whether or not the KB already has the concept. A sense spelled
  `physical-object` and a type spelled `physical_object` are two terms, and no check
  compares a sense's word half with the types already stored. Canonical form merges
  sentences that differ only in variable names or argument order, never two symbols. A
  duplicate type therefore splits everything the engine does: a rule written on one name
  does not fire on facts under the other, an argument declaration derives one name and a
  query asks the other, and `disjointness-audit` reads the pair `:unknown` until someone
  relates them.
- **Maintenance.** A duplicate found late has facts, rules, argument declarations and
  separations under both names. The merge has to choose a survivor, move each sentence and
  check each rule, where the search before minting would have cost one query.

**Why not the other ways.**

- **Searching only the file being edited.** The upper and middle files are term-centric
  and split by subject, so a concept used in one file is often defined in another.
- **Searching by name only.** A synonym, a sense or a broader type with the case in its
  comment is missed, and those are the duplicates that last longest.
- **Recalling the vocabulary.** Memory of a KB is a snapshot of an older KB. **walk down**
  ([ch. 10](10-parent.md)) asks for the direct specs to be queried for the same reason.

**Audit.** The change lists, for each new term, where it searched and what it found, with
the reason each near match was not reused. A reviewer runs `describe` on each new term and
on each near match the change names, and compares their `:genls`, `:specs` and comments.

## When the search finds a near match

**Practice.** Decide among four outcomes, in this order:

1. **Reuse.** The existing term means what the change needs. Use it.
2. **Specialize.** The change needs a narrower kind. Mint it below the existing term, with
   its `genl`, its separations from siblings and its comment ([ch. 6](06-definitional-block.md)).
3. **Disambiguate.** One word names two concepts. Mint a sense for each meaning, spelled
   as the word, a dash and a lowercase disambiguator, and record what each means.
4. **Mint.** Nothing found means the same thing or a broader thing. Mint the term, and
   state in the change why the near matches do not fit.

**Example.** The search for an `ability` type finds `able` and the event kinds
in abstract.txt, and the outcome is reuse: an ability is an event kind, so the change
writes no new type and states the ability with the existing relation (CxBiology.txt):

```clojure
(abilityType bird flying)
```

A word read from text with two meanings takes the third outcome: `abandonment-romantic`
and `abandonment-dual` are two senses, each a type with its own `genl` and comment. A
surface form whose meaning is not yet decided is a lexeme in the `lex/` namespace, such as
`lex/fool's_gold`, until a sense replaces it.

**Why.**

- **Logic.** Reuse and specialization keep one representation per concept, and a
  specialization's `genl` states exactly how the new concept relates to the old one.
- **Engine.** A specialization inherits its parent's separations, its parent's argument
  declarations reach it, and rules on the parent fire on its members, so the new term
  joins everything the KB already does with the old one. A sense is a type like any other,
  so the hierarchy holds two senses apart as it holds any two types apart.
- **Maintenance.** A reviewer who sees the near matches and the reason for each decision
  can check the decision. A reviewer who sees only the new term has to repeat the search.

**Why not the other ways.** Minting beside a near match without a relation between them
leaves two unrelated nodes for related concepts, so the audit reads them `:unknown` and no
rule crosses between them. Overloading the existing term with the second meaning makes
every rule on it true of one meaning and false of the other, which **does it have
rules?** ([ch. 1](01-true-and-useful.md)) rules out.

**Audit.** For each new term with a near match, the change states which of the four
outcomes it took and why. `disjointness-audit` run after the change shows each new term's
pairs with its near matches: a pair that reads `:unknown` is a relation the change has not
stated.
