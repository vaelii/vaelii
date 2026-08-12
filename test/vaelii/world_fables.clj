;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.world-fables
  "Children's stories as contexts — worked examples, test-world data below the
  shipped schema (see vaelii.world).

  Each fable is a context under CxStories (which sees the shipped upper ontology
  through CxWell, so the characters get their types).  A story holds a few typed
  characters, the facts of
  the tale, and rules whose *connected conjunctive antecedents* join those facts to
  DERIVE the story's moral — the moral is a computed conclusion, not a stored string.

    * The Lion and the Mouse   — a kindness is repaid (a rule joined on both actors).
    * The Tortoise and the Hare — steadiness beats overconfidence (a 3-way join).
    * The Ant and the Grasshopper — preparation pays (derived facts feed a further rule).
    * The Boy Who Cried Wolf   — a liar is not believed even when truthful; the belief
      is a defeasible default defeated by a *more specific* exception (keyed on the
      narrower type `liar`), echoing the penguin — and the wolf really comes, so a
      joined rule (with a constant character) derives the boy's unheeded danger.

  A human-readable moral is attached to each story context as a `comment` sentex, so
  the KB narrates itself in its own representation."
  (:require [vaelii.core :as v]))

;; ---- contexts -----------------------------------------------------------

(def context-links
  "Each fable is an isolated leaf under CxStories, which hangs off CxWell.
  A story sees the shared upper ontology and the middle theories (through CxWell)
  plus universally-lifted facts — but NOT the contingent facts of the sibling data
  contexts (CxNaturalWorld, CxSocialWorld): a rule joining a story fact with
  a natural-world fact would never fire, since their placement intersection is empty.
  Each story is self-contained."
  '[(genlCx CxStories        CxWell)
    (genlCx CxLionMouse      CxStories)
    (genlCx CxTortoiseHare   CxStories)
    (genlCx CxAntGrasshopper CxStories)
    (genlCx CxCriedWolf      CxStories)])

;; ---- the narrative predicates, documented -------------------------------

(def predicate-docs
  '[(comment spared             "(spared ?strong ?weak) means that ?strong showed mercy and let ?weak go.")
    (comment freed              "(freed ?rescuer ?captive) means that ?rescuer set ?captive loose.")
    (comment trapped            "(trapped ?animal) means that ?animal is caught and cannot escape unaided.")
    (comment repaidKindness     "(repaidKindness ?animal1 ?animal2) means that ?animal1 returned an earlier kindness of ?animal2. The derived moral of the Lion and the Mouse.")
    (comment raced              "(raced ?animal1 ?animal2) means that ?animal1 and ?animal2 ran a race against each other.")
    (comment persevered         "(persevered ?animal) means that ?animal kept going steadily to the end.")
    (comment overconfident      "(overconfident ?animal) means that ?animal was sure of winning and grew careless.")
    (comment napped             "(napped ?animal) means that ?animal stopped to sleep midway.")
    (comment wins               "(wins ?animal1 ?animal2) means that ?animal1 beats ?animal2. The derived moral of the Tortoise and the Hare.")
    (comment preparedForWinter  "(preparedForWinter ?animal) means that ?animal laid in provisions during the good season.")
    (comment idledInSummer      "(idledInSummer ?animal) means that ?animal played instead of preparing.")
    (comment survivesWinter     "(survivesWinter ?animal) means that ?animal comes through the hard season. Derived from having prepared.")
    (comment suffersInWinter    "(suffersInWinter ?animal) means that ?animal goes hungry in the hard season. Derived from having idled.")
    (comment betterPreparedThan "(betterPreparedThan ?animal1 ?animal2) means that ?animal1 fared better than ?animal2 by preparing. The derived moral of the Ant and the Grasshopper.")
    (comment liedBefore         "(liedBefore ?person) means that ?person has raised a false alarm in the past.")
    (comment liar               "Someone who has raised a false alarm — a person whose word is no longer trusted.")
    (comment criesWolf          "(criesWolf ?person) means that ?person raises the alarm that a wolf is coming.")
    (comment approaches         "(approaches ?predator ?victim) means that ?predator is closing in on ?victim.")
    (comment believed           "(believed ?person) means that ?person's alarm is trusted. A default, defeated for a known liar.")
    (comment inDanger           "(inDanger ?person) means that ?person faces a real threat.")])

(def predicate-types
  "Arity memberships for the narrative predicates, upholding the KB's self-classifying
  invariant (every predicate is a unary/binary/… predicate)."
  '[(binaryPredicate spared)  (binaryPredicate freed)  (binaryPredicate repaidKindness)
    (binaryPredicate raced)   (binaryPredicate wins)   (binaryPredicate betterPreparedThan)
    (binaryPredicate approaches)
    (unaryPredicate trapped)  (unaryPredicate persevered) (unaryPredicate overconfident)
    (unaryPredicate napped)   (unaryPredicate preparedForWinter) (unaryPredicate idledInSummer)
    (unaryPredicate survivesWinter) (unaryPredicate suffersInWinter) (unaryPredicate liedBefore)
    (unaryPredicate criesWolf) (unaryPredicate believed) (unaryPredicate inDanger)
    (unaryPredicate liar)])

(def morals
  "The human-readable moral of each fable, attached to its context."
  '[(comment CxLionMouse      "The Lion and the Mouse — moral: no kindness, however small, is ever wasted.")
    (comment CxTortoiseHare   "The Tortoise and the Hare — moral: slow and steady wins the race.")
    (comment CxAntGrasshopper "The Ant and the Grasshopper — moral: prepare in the good times for the hard times.")
    (comment CxCriedWolf      "The Boy Who Cried Wolf — moral: a liar is not believed even when he tells the truth.")])

;; ---- the same four stories, in English ----------------------------------

(def texts
  "Each fable as prose, keyed by its context — the **input** side of the reading
  pipeline (`vaelii.impl.llm.text`), against which the formal version below is the
  ground truth (`vaelii.impl.llm.score`).

  Written as a retelling rather than as a transliteration of the sentexes: the sentences
  are ones a reader would write, the characters are introduced by their kind rather than
  by the name the modeller gave them, and the general claims are stated the way a fable
  states its moral.  A text that spelled the s-expressions out in words would score well
  and measure nothing.

  What it *does* share with the formal version is vocabulary, and that is worth stating
  plainly: the narrative predicates were named after the English words the fable uses
  (`spared`, `napped`, `preparedForWinter`), so resolving a word to a term is easier here
  than it would be on arbitrary prose.  The score is a floor on the formalism, not a claim
  about English."
  {'CxLionMouse
   (str "A lion caught a mouse in his paw, but he spared the little creature and let "
        "it go. Not long afterwards the lion himself was trapped in a hunter's net. "
        "The mouse heard him roaring, came running, and freed him by gnawing through "
        "the ropes. Whoever is spared will, given the chance, free the one who spared "
        "them, and so repay the kindness.")

   'CxTortoiseHare
   (str "A tortoise and a hare raced each other along the road. The hare was "
        "overconfident, so certain of winning that he lay down and napped in the "
        "shade. The tortoise persevered, plodding on without once stopping. When two "
        "animals race, and the slower one perseveres while the faster one naps, the "
        "slower one wins.")

   'CxAntGrasshopper
   (str "All through the warm months the ant prepared for winter, carrying grain down "
        "into her nest, while the grasshopper idled in summer and sang. Whoever "
        "prepared for winter survives winter. Whoever idled in summer suffers in "
        "winter. And one who survives the winter was better prepared than one who "
        "suffers it.")

   'CxCriedWolf
   (str "The boy who watched the sheep had lied before, raising a false alarm for the "
        "fun of seeing the village run. A liar is a kind of person, one whose word is "
        "no longer trusted, and anyone who has lied before is a liar. Today the boy "
        "cries wolf again, and this time a wolf really is approaching him. A cry is "
        "believed by default, except from a liar: a liar who cries wolf is not "
        "believed. The danger is real all the same, for whenever the wolf is "
        "approaching someone who cries wolf, that person is in danger.")})

;; ---- the stories --------------------------------------------------------

(defn- assert-all [kb ctx forms] (doseq [s forms] (v/assert kb s ctx)))

(defn- lion-and-mouse [kb]
  (assert-all kb 'CxLionMouse
              '[(lion LionA) (mouse MouseA)
                (spared LionA MouseA)                 ; the lion let the mouse go
                (trapped LionA)                       ; later the hunters catch the lion
                (freed MouseA LionA)])                ; the mouse gnaws the net and frees him
  ;; a kindness given and later returned makes a repaid kindness (joined on both actors)
  (v/assert-rule kb '[(spared ?strong ?weak) (freed ?weak ?strong)]
                 '(repaidKindness ?weak ?strong) 'CxLionMouse))

(defn- tortoise-and-hare [kb]
  (assert-all kb 'CxTortoiseHare
              '[(tortoise TortoiseA) (hare HareA)
                (raced TortoiseA HareA)
                (persevered TortoiseA)
                (overconfident HareA)
                (napped HareA)])
  ;; the steady racer beats the fast one who stops to sleep (a three-antecedent join)
  (v/assert-rule kb '[(raced ?slow ?fast) (persevered ?slow) (napped ?fast)]
                 '(wins ?slow ?fast) 'CxTortoiseHare))

(defn- ant-and-grasshopper [kb]
  (assert-all kb 'CxAntGrasshopper
              '[(ant AntA) (grasshopper GrasshopperA)
                (preparedForWinter AntA)
                (idledInSummer GrasshopperA)])
  ;; preparing carries you through; idling does not; the one who prepared fares better
  (v/assert-rule kb '[(preparedForWinter ?x)] '(survivesWinter ?x)  'CxAntGrasshopper)
  (v/assert-rule kb '[(idledInSummer ?x)]     '(suffersInWinter ?x) 'CxAntGrasshopper)
  (v/assert-rule kb '[(survivesWinter ?a) (suffersInWinter ?b)]     ; derived facts joined
                 '(betterPreparedThan ?a ?b) 'CxAntGrasshopper))

(defn- boy-who-cried-wolf [kb]
  ;; A liar is a narrower kind of speaker than a person.  Nothing is arbitrated here:
  ;; the belief rule states its own exception with `exceptWhen`, so for a liar it
  ;; concludes nothing and there is no clash to resolve.  The `genl` edge is what lets
  ;; the exception be stated at the type rather than at every liar individually.
  (v/assert kb '(genl liar person) 'CxCriedWolf)
  (assert-all kb 'CxCriedWolf
              '[(human BoyA) (wolf WolfA)
                (liedBefore BoyA)                     ; he has raised false alarms
                (criesWolf BoyA)                      ; now he cries wolf again
                (approaches WolfA BoyA)])             ; and this time the wolf is real
  ;; having raised a false alarm is what makes him one
  (v/assert-rule kb '[(liedBefore ?x)] '(liar ?x) 'CxCriedWolf)
  ;; a cry is believed by default — **except** from a liar.  The exception rides on
  ;; the rule (`exceptWhen`), so for a liar the rule concludes nothing at all.
  ;;
  ;; This is the harder of the two bundled cases, and deliberately so: `liar` is not
  ;; asserted, it is *derived* by the rule above.  So the exception depends on what
  ;; another rule concludes, and whether it holds can only be known after that rule has
  ;; fired — which is exactly the dependency stratification would order.  See
  ;; docs/exceptions.md, Status, for what measuring this actually showed.
  (v/assert kb '(exceptWhen (liar ?x)
                            (set/defaultRule (implies (and (criesWolf ?x)) (believed ?x))))
            'CxCriedWolf)
  ;; … and the positive claim that a liar's cry is not believed stands on its own,
  ;; queryable, rather than existing only to defeat the rule above
  (v/assert-rule kb '[(liar ?x) (criesWolf ?x)] '(not (believed ?x)) 'CxCriedWolf)
  ;; the danger is real all the same: an approaching predator + the cry ⇒ real danger
  ;; (a joined rule with a constant character, WolfA, in an antecedent)
  (v/assert-rule kb '[(approaches WolfA ?victim) (criesWolf ?victim)]
                 '(inDanger ?victim) 'CxCriedWolf))

(defn load-into
  "Load the story contexts into `kb` (which must already have the starter
  ontology).  Returns kb."
  [kb]
  (doseq [s context-links] (v/assert kb s 'CxUniverse))
  (assert-all kb 'CxStories predicate-docs)
  (assert-all kb 'CxStories predicate-types)
  (assert-all kb 'CxStories morals)
  (lion-and-mouse kb)
  (tortoise-and-hare kb)
  (ant-and-grasshopper kb)
  (boy-who-cried-wolf kb)
  kb)
