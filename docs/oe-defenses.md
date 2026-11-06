# Ontology defenses

- **Covers:** why a piece of the shipped ontology is shaped the way it is, and why the representation a reader would reach for instead is worse.
- **Not here:** the general rules every vocabulary change follows. Those are in [oe-principles.md](oe-principles.md), and an entry here cites a principle by its handle rather than restating it.
- **Assumes:** you have read the vocabulary the entry defends, in the KB file it names.

An entry names the alternative, says what the KB states instead, and gives the reason.

## Space, time and mass

### Mass and location are two axes, not one

**Alternative:** `intangible` means "has no mass", and everything without mass is one kind.

**Instead:** `thing` is partitioned three ways, each on its own axis: `(partition thing tangible intangible)` by mass, `(partition thing spatial aspatial)` by location in space, and `(partition thing temporal atemporal)` by location in time. `nowhere_never` names what is aspatial and atemporal.

**Why:** mass and location come apart. A region of space has a location and no mass. A line such as y=x is placed in a space and has no mass. A number has neither. With one axis, "massless" sweeps a region together with a number, and every rule about located things has to exclude the massless ones by hand. With three axes, each rule names the axis it is about, and the disjointness audit reads the pairs between axes as overlapping.


### An event is temporal, and has no place as such

**Alternative:** `(genl event spatiotemporal)`: every event happens somewhere and somewhen.

**Instead:** `event` is temporal, through `(genl situation temporal)` in `core.txt`, and the KB states no place for an event as such.

**Why:** some events have a time and no place. A contract expiring, a debt falling due and a term of office ending each happen at a time and nowhere in particular, and each can cause things. Requiring a place would either exclude them from `event` or force an invented location.


### `orthogonal` for axes that cut across each other

**Alternative:** relate cross-cutting types with `disjoint` or `separating`, or leave their relationship unstated.

**Instead:** `(orthogonal A B)` states that A and B overlap and neither subsumes the other, for example `made` and `biological`.

**Why:** the types on different axes are neither disjoint nor nested. A bred animal is made and biological. Left unstated, every such pair reads `:unknown` in the disjointness audit, which hides the pairs that are open questions among hundreds that are settled. Stating them disjoint would be false. `orthogonal` records the settled overlap, so the audit's unknowns are the real open questions. An `orthogonal` is not inherited along `genl` ([taxonomy.md](taxonomy.md#disjointness)), so `abstract.txt` states each overlapping pair below `(orthogonal biological made)` as its own sentence, such as `(orthogonal organism made)` for a cloned sheep and `(orthogonal body_part natural)` for a heart.


## Time and change

### `transitiveInArg` points the way Cyc's does

**Alternative:** give `transitiveInArg` and `transitiveInArgInverse` the directions opposite to Cyc's `transitiveViaArg` and `transitiveViaArgInverse`.

**Instead:** each name carries the direction of the Cyc predicate it matches, and a test asserts the direction each carries along `genl`.

**Why:** readers arrive from Cyc's documentation. A predicate whose name matches Cyc's and whose direction is opposite gets used backwards, and the result is a KB that derives the wrong memberships with no error. Apart from Cyc, this direction is also the one most readers expect the name to mean.


## Kinds and properties

### Abilities are event kinds, not an `ability` type

**Alternative:** an `ability` type whose instances are abilities (flying, swimming), related to their holders by `able`.

**Instead:** no `ability` type. The second argument of `able` and `abilityType` is an event kind: flying and travelling are kinds of event.

**Why:** an ability is an ability to take part in a kind of event, and the event vocabulary already carries the structure abilities need. `(genl flying travelling)` makes "can fly implies can travel" fall out of the event hierarchy with no parallel ability hierarchy to keep in step, and travelling being a `causal_event` is stated once, for the events and the abilities together.


### An event's doer is a thing

**Alternative:** type `doneBy`'s second argument as `agent`, `animal` or `organism`, so that only something that can act brings an event about.

**Instead:** `abstract.txt` declares `thing` on the second argument of `doneBy` and of its spec `performedBy`.

**Why:** a machine, a process or a storm brings events about as well as a person or an animal does. `agent` names a registered participant rather than something that can act, and no type below `thing` covers every doer. A narrower type on the position would conclude every doer a member of it under the assertive reading, a machine included. `performedBy`, the intentional case, carries the narrower claim.


### Food and body part overlap

**Alternative:** `(disjoint food body_part)`: something eaten is not a part an organism grew.

**Instead:** `abstract.txt` states `(orthogonal food body_part)`.

**Why:** a leg of lamb and a chicken wing are each a body part and food at once. A `disjoint` over the pair places a clash for every such membership. A KB that needs the two kept apart for its own purpose states a separation over narrower kinds of its own.


### Biology properties have genls

**Alternative:** keep `alive`, `dead`, `mortal`, `asleep`, `awake`, `breathes_air` and `warm_blooded` free of genls, on the rule that a property is not a type.

**Instead:** each property takes the genl it is true of: `alive` and `dead` under `biological`, and the other five under `organism` or `animal`.

**Why:** only a living kind of thing can be alive, asleep or warm-blooded. Without a genl, nothing stops `(warm_blooded Rock1)`, and every pair of these properties with the kinds below `organism` reads `:unknown` in the audit. With the genl, a misapplied property is caught as a type clash. `alive` and `dead` go under `biological` rather than `organism`, so a dead leaf is not concluded to be an organism.


### A kind may sit below a property

**Alternative:** let a biology property have a genl but no spec, on the rule that a property is said of a kind and so nothing may be placed under it.

**Instead:** a kind may be placed under a property it always has. CxBiology states `(genl bird warm_blooded)` and `(genl mammal warm_blooded)`. Whether a name is spelled as a noun or as an adjective is a style hint, not a rule of the hierarchy.

**Why:** "every bird is warm-blooded" is a genl edge from `bird` to `warm_blooded`, and nothing in it makes `warm_blooded` a kind that birds are a sort of. OntoClean allows a non-sortal above a sortal. It forbids an anti-rigid type above a rigid one: a property a thing can stop having cannot subsume a kind a thing never stops being.


### Metal is solid by default, and mercury is the stated exception

**Alternative:** state that every metal is solid, or leave `metal_stuff`'s state of matter unstated.

**Instead:** in CxNormalPhysicalConditions, the states of matter at room temperature, `metal_stuff` is a `solid` by default, and mercury is the stated exception.

**Why:** a monotonic "every metal is solid" is false, because mercury is liquid at room temperature. Leaving the state unstated gives up a conclusion that is right for almost every metal anyone will mention. A default states the common case, and the exception keeps the one known counterexample from contradicting it. The choice between a default and a list of the known solid metals turns on new cases: a newly discovered metal, a hypothesized one, or one in a fictional or counterfactual context should come out solid unless something says otherwise. A list would conclude nothing about any of them, so the default is the right form (**default or enumerate** in the principles).


## Logic

### `empty` and `nonempty` partition `unary_predicate`

**Alternative:** leave it implicit that a type below two disjoint types has no members.

**Instead:** `(partition unary_predicate empty nonempty)`, carried down and up `genl`. A type below two disjoint types is concluded `empty`, and the disjointness audit does not treat a shared subtype as evidence of overlap unless the subtype is known to be `nonempty`.

**Why:** `(disjoint c c)` holds exactly when c is empty, so an empty type is disjoint from everything, itself included. Left implicit, an empty shared subtype would be counted as an overlap witness and the audit would report two disjoint types as overlapping. Naming emptiness makes that case explicit, so the audit can ask for a witness that something is actually there.

