;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.tokens
  "A bidirectional **token dictionary** — `path-token ↔ int` — the first new durable
  ground truth the dense (`:memory-columnar`) index rests on.

  The columnar trie (`vaelii.impl.columnar`) labels its edges with `int` tokens rather
  than boxed structured values, so it needs a stable `token → int` map and an `int →
  token` inverse to decode a node's child tokens back for `children`.  A *token* is
  whatever a trie path level can be (`sentex/path`): a symbol (predicate / individual /
  type / context), a number, a keyword (`:false` / `:rule`), `nil` (a rule's assumption
  / constraint slot), a `[::subterm k]` arity marker, or a whole literal list (a
  `:false` body, a rule's antecedent vector).  They arrive already canonical from
  `sentex/path` (the sentence went through `sentex/canon`), so the dictionary interns
  them **as-is** — re-canonicalizing would turn a marker vector into a list and break
  `sentex/subterm-mark?`, exactly as the current `KvIndexStore` relies on raw path
  tokens as keys.

  **Content-keyed, first-writer-wins.**  An id is allocated the first time a token is
  seen and never changes; ids count up from 0 (array-friendly).  The id *value* depends
  on first-encounter order, but the index's correctness does not — an id is an opaque
  edge label the inverse map decodes — so a rebuild from the records (`reindex` / `recover`)
  that re-interns in a different order yields an equal index (identical lookups), which
  is the order-independence that matters.  A durable columnar index that persisted its
  `int` edges would instead load this dictionary before reading them; that is the format
  Phase 2's durable variant uses.

  **Keyed by Clojure equality, not Java's** — see `Key` below.  That is not a refinement;
  it is what makes this dictionary answer the same questions the flat map it replaces
  answers.

  **Single-writer**, like the index it serves: the maps are mutated in place under the
  one-writer contract, no atom.

  A held namespace (`vaelii.impl.types.prover` states what that means): it defines the `Key` and `TokenDict` types and the `ITokens` protocol, and requires no vaelii namespace, so the development browser's reloader never re-evaluates it, and an edit to it takes a restart."
  (:import [java.util HashMap ArrayList]))

;; The flat-map index keys its trie on a `PersistentHashMap`, so two tokens that are
;; Clojure-`=` are one key: `(= 2 (int 2))` is true, and a path carrying an `Integer`
;; reaches a node stored under a `Long`.  A `java.util.HashMap` keyed on the token itself
;; says `Integer(2).equals(Long(2))` — **false** — and the node is simply not found.  No
;; error, no warning: one fewer answer, on a backend that is meant to be set-equal.
;;
;; The two boxings genuinely meet, because a path token can arrive from arithmetic as
;; easily as from a literal: `agg/count` concludes `(childCount Ann 2)` with an `Integer`,
;; and the same sentence asked as a question carries a `Long`.  A whole literal list is a
;; token too, so the disagreement nests — `(f 2)` and `(f (int 2))` are one Clojure key
;; and two Java ones.
;;
;; `Key` restores the flat map's semantics exactly, by deferring to the same two methods
;; it uses: `hasheq` (which hashes every integral width alike) and `equiv`.  The cost is
;; one small wrapper per intern/lookup, which is what correctness against the reference
;; index is worth.
(deftype Key [v]
  Object
  (hashCode [_] (clojure.lang.Util/hasheq v))
  (equals [_ o] (and (instance? Key o) (clojure.lang.Util/equiv v (.-v ^Key o)))))

(defprotocol ITokens
  (intern-token! [d tok] "The id for `tok`, allocating a fresh one (first-writer-wins) if absent.")
  (token-id      [d tok] "The existing id for `tok`, or -1 — no allocation (the absent-path fast exit).")
  (id-token      [d id]  "The token an id decodes to (`nil` is a real token).")
  (token-count   [d]     "How many distinct tokens are interned.")
  (clear-tokens! [d]     "Drop every mapping (the whole-dictionary wipe `clear-index!` needs)."))

;; `fwd` maps `Key`-wrapped token → boxed Integer id; `rev` is id-indexed (rev.get(id) =
;; token, **unwrapped**, so `id-token` hands back exactly what the path carried), which
;; makes the inverse an O(1) array read.  `nil` is a legal token (a HashMap allows a null
;; key and an ArrayList a null element), so it round-trips like any other.
(deftype TokenDict [^HashMap fwd ^ArrayList rev]
  ITokens
  (intern-token! [_ tok]
    (let [id (.get fwd (Key. tok))]
      (if id
        (int id)
        (let [nid (.size rev)]
          (.put fwd (Key. tok) (Integer/valueOf nid))
          (.add rev tok)
          nid))))
  (token-id [_ tok]
    (let [id (.get fwd (Key. tok))] (if id (int id) -1)))
  (id-token [_ id] (.get rev (int id)))
  (token-count [_] (.size rev))
  (clear-tokens! [_] (.clear fwd) (.clear rev) nil))

(defn token-dict [] (->TokenDict (HashMap.) (ArrayList.)))
