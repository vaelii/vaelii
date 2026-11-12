;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.direction-test
  "Directed rules via the set/forwardRule, set/backwardRule, set/inertRule virtual
  predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb forward-rule-materializes
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/forwardRule ancestor-rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "a forward rule forward-chains its consequent"
      (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam))))))

(tu/deftest-kb backward-rule-does-not-materialize-but-proves
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/backwardRule ancestor-rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "a backward rule is not forward-materialized"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam))))
    (testing "but it answers backward queries"
      (is (v/provable? kb (list ancestorOf tom bob) 'CxFam)))))

(tu/deftest-kb inert-rule-is-documentation-only
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/inertRule ancestor-rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "an inert rule drives no inference"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam)))
      (is (not (v/provable? kb (list ancestorOf tom bob) 'CxFam))))
    (testing "but the rule sentex is stored and findable by its terms"
      (is (= 1 (count (v/find-sentexes kb ancestorOf)))))
    ;; Documentation is only documentation if it is *there*: believed like any other
    ;; rule, and posted under its predicates so a browser and a term search find it.
    ;; Not firing is the direction's doing, not an absence of either of those — which
    ;; is what separates this from `assert-inert`, whose sentex nothing believes
    ;; (docs/inference.md, "An inert rule is documentation with a handle").
    (let [h (v/handle-of kb (list 'set/inertRule ancestor-rule) 'CxFam)]
      (testing "the rule is believed, at an ordinary class — there is no :inert strength"
        (is (v/in? kb h))
        (is (= :default (:strength (v/sentex kb h))))
        (is (= :default (v/defeat-class kb h)))
        (is (= #{} (:engines (v/sentex kb h)))))
      (testing "and it is indexed both ways, which is what makes it browsable"
        (is (contains? (set (reads/as-stored-rules-by-consequent-global (:index kb) ancestorOf)) h))
        (is (contains? (set (reads/as-stored-rules-by-antecedent-global (:index kb) parentOf)) h))))))

(tu/deftest-kb a-transitivity-rule-is-written-down-inert-while-the-closure-answers
  ;; The pattern `docs/taxonomy.md` describes: transitivity is not run as a rule — the
  ;; closure answers it — so the rule is written down inert, where a reader looks for it.
  ;; The closure keeps answering with the rule sitting there, and the rule adds no
  ;; derived sentex of its own: asserting it bare would materialize one per pair.
  (tu/with-terms [animal_ dog_ terrier_ Rex]
    (let [rule (vr/rule-sentence [(list 'genl '?a '?b) (list 'genl '?b '?c)]
                                 (list 'genl '?a '?c))]
      (v/assert kb (list 'set/inertRule rule) 'CxUniverse)
      (v/assert kb (list 'genl terrier_ dog_) 'CxUniverse)
      (v/assert kb (list 'genl dog_ animal_) 'CxUniverse)
      (v/assert kb (list terrier_ Rex) 'CxUniverse)
      (testing "the closure answers the transitive question the rule describes"
        (is (v/genl? kb terrier_ animal_))
        ;; ...and a query at the supertype reaches the instance through it.  `ask`, not
        ;; `sentexes-matching`: the closure is answered on demand and stores no edge, so
        ;; there is no `(animal Rex)` sentex to match — which is the whole design.
        (is (v/provable? kb (list animal_ Rex) 'CxUniverse))
        (is (= [{'?w Rex}] (v/ask kb (list animal_ '?w) 'CxUniverse))))
      (testing "while the rule itself derives nothing"
        (is (empty? (v/sentexes-matching kb (list 'genl terrier_ animal_)
                                         'CxUniverse))
            "no materialized (genl terrier animal) — the closure is not a stored edge")))))

(tu/deftest-kb direction-via-opts
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'CxFam {:direction :backward})
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing ":direction opt matches the virtual-predicate behavior"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam)))
      (is (v/provable? kb (list ancestorOf tom bob) 'CxFam)))))

(tu/deftest-kb assert-rule-takes-every-direction-its-docstring-names
  ;; `:both` is `:forward`'s class (docs/inference.md), so it stores the rule `:forward`
  ;; stores; `assert-rule` wraps the sentence and must not also hand `assert` the opt.
  (doseq [d [:forward :backward :inert :both]]
    (let [p (tu/tmp-pred) q (tu/tmp-pred) a (tu/tmp-ind)
          h (v/assert-rule kb [(list p '?x)] (list q '?x) 'CxFam {:direction d})]
      (v/assert kb (list p a) 'CxFam)
      (testing (str d)
        (is (= ({:forward #{:forward :backward} :both #{:forward :backward}
                 :backward #{:backward} :inert #{}} d)
               (:engines (v/sentex kb h))))
        (is (= (contains? #{:forward :both} d)
               (some? (v/handle-of kb (list q a) 'CxFam))))))))

(tu/deftest-kb bare-rule-is-backward-by-default
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb rule 'CxFam)                                  ; a bare implies
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (testing "a bare rule is backward by default — it does not forward-materialize"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam)))
      (is (= #{:backward} (:engines (v/sentex kb (v/handle-of kb rule 'CxFam))))))
    (testing "but it still answers backward queries"
      (is (v/provable? kb (list ancestorOf tom bob) 'CxFam)))))

(tu/deftest-kb forward-only-rule-forward-chains-but-is-not-backward-usable
  ;; The fourth direction, a tests-only mode: set/forwardOnlyRule forward-chains like
  ;; set/forwardRule but is never used in backward proof.  The shipped ontology uses
  ;; set/forwardRule (forward + backward), never this.
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/forwardOnlyRule rule) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (let [sx (v/sentex kb (v/handle-of kb (list 'set/forwardOnlyRule rule) 'CxFam))]
      (testing "the record carries #{:forward}"
        (is (= #{:forward} (:engines sx))))
      (testing "it forward-chains its consequent, like a forward rule"
        (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'CxFam))))
      (testing "the chainers read it forward-capable but not backward-capable"
        (is (vr/forward-sentex? sx))
        (is (not (vr/backward-sentex? sx)))))))

(tu/deftest-kb a-forward-rule-reads-a-lazy-forward-conclusion-and-not-a-backward-one
  (tu/with-terms [cat feline noted ownerOf Tom Ann]
    (let [rule   (vr/rule-sentence [(list cat '?x)] (list feline '?x))
          held?  #(boolean (when-let [h (v/handle-of kb % 'CxFam)] (v/in? kb h)))
          member (v/assert kb (list cat Tom) 'CxFam)]
      (v/assert kb (list 'set/backwardRule rule) 'CxFam)
      (v/assert kb (list 'set/forwardRule
                         (vr/rule-sentence [(list ownerOf Ann '?x) (list feline '?x)] (list noted '?x)))
                'CxFam)
      (v/assert kb (list ownerOf Ann Tom) 'CxFam)
      (testing "a backward rule's conclusion is not read by a forward join"
        (is (false? (held? (list noted Tom))))
        (is (v/provable? kb (list feline Tom) 'CxFam)))
      (v/assert kb (list 'set/lazyForwardRule rule) 'CxFam)
      (testing "re-asserted lazy-forward, its conclusion is read and is not stored"
        (is (= #{:backward :lazy} (:engines (v/sentex kb (v/handle-of kb rule 'CxFam)))))
        (is (true? (held? (list noted Tom))))
        (is (nil? (v/handle-of kb (list feline Tom) 'CxFam))))
      (v/retract! kb member)
      (testing "the firing rests on the membership the lazy-forward rule read"
        (is (false? (held? (list noted Tom))))))))

(tu/deftest-kb a-lazy-firing-is-placed-where-no-visible-edge-holds-its-membership
  (doseq [edge-first? [true false]]
    (tu/with-terms [dog vocal hasVoice Rex Bark CxA CxB]
      (let [held? #(boolean (when-let [h (v/handle-of kb % CxA)] (v/in? kb h)))
            edge  #(v/assert kb (list 'genl dog vocal) CxB)]
        (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
        (when edge-first? (edge))
        (v/assert kb (list 'set/lazyForwardRule
                           (vr/rule-sentence [(list dog '?x)] (list hasVoice '?x Bark)))
                  CxA)
        (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list hasVoice '?x '?v)] (list vocal '?x)))
                  CxA)
        (v/assert kb (list dog Rex) CxA)
        (when-not edge-first? (edge))
        (is (held? (list vocal Rex)) (str "edge first: " edge-first?))))))

(defn- lazy-voice-world!
  "The lazy rule `(dog ?x) ⇒ (hasVoice ?x Bark)`, its reader `(hasVoice ?x ?v) ⇒ (vocal ?x)`
  and `(dog Rex)`, all in `cx`."
  [kb cx dog vocal hasVoice Rex Bark]
  (v/assert kb (list 'set/lazyForwardRule (vr/rule-sentence [(list dog '?x)] (list hasVoice '?x Bark))) cx)
  (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list hasVoice '?x '?v)] (list vocal '?x))) cx)
  (v/assert kb (list dog Rex) cx))

(tu/deftest-kb a-departing-edge-re-joins-the-lazy-reader-whose-membership-it-held
  (doseq [edge-first? [true false]]
    (tu/with-terms [dog vocal hasVoice Rex Bark CxA]
      (let [stored? #(boolean (when-let [h (v/handle-of kb % CxA)] (v/in? kb h)))
            edge    #(v/assert kb (list 'genl dog vocal) CxA)
            e0      (when edge-first? (edge))]
        (lazy-voice-world! kb CxA dog vocal hasVoice Rex Bark)
        (v/retract! kb (or e0 (edge)))
        (is (stored? (list vocal Rex)) (str "edge first: " edge-first?))))))

(tu/deftest-kb a-departing-edge-re-joins-the-lazy-reader-beside-a-member-of-a-subtype
  (doseq [edge-first? [true false]]
    (tu/with-terms [dog puppy vocal hasVoice Rex Bark CxA]
      (let [held? #(boolean (when-let [h (v/handle-of kb % CxA)] (v/in? kb h)))
            edge  #(v/assert kb (list 'genl puppy vocal) CxA)
            e0    (when edge-first? (edge))]
        (v/assert kb (list 'genl puppy dog) CxA)
        (v/assert kb (list 'set/lazyForwardRule (vr/rule-sentence [(list dog '?x)] (list hasVoice '?x Bark))) CxA)
        (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list hasVoice '?x '?v)] (list vocal '?x))) CxA)
        (v/assert kb (list puppy Rex) CxA)
        (v/retract! kb (or e0 (edge)))
        (is (held? (list vocal Rex)) (str "edge first: " edge-first?))))))

(tu/deftest-kb a-genl-edge-leaves-a-lazy-reader-s-membership-its-taxonomy-holds-unstored-in-either-order
  (doseq [edge-first? [true false]]
    (tu/with-terms [dog vocal hasVoice Rex Bark CxA]
      (when edge-first? (v/assert kb (list 'genl dog vocal) CxA))
      (lazy-voice-world! kb CxA dog vocal hasVoice Rex Bark)
      (when-not edge-first? (v/assert kb (list 'genl dog vocal) CxA))
      (is (nil? (v/handle-of kb (list vocal Rex) CxA)) (str "edge first: " edge-first?))
      (is (v/provable? kb (list vocal Rex) CxA) (str "edge first: " edge-first?)))))

(tu/deftest-kb a-lazy-reader-s-membership-its-taxonomy-holds-stays-unstored-when-a-second-edge-re-joins-the-reader
  (tu/with-terms [dog puppy vocal hasVoice Rex Pup Bark CxA]
    (v/assert kb (list 'genl puppy dog) CxA)
    (v/assert kb (list puppy Pup) CxA)
    (lazy-voice-world! kb CxA dog vocal hasVoice Rex Bark)
    (v/assert kb (list 'genl dog vocal) CxA)
    (v/assert kb (list 'genl puppy vocal) CxA)
    (is (nil? (v/handle-of kb (list vocal Rex) CxA)))
    (is (v/provable? kb (list vocal Rex) CxA))))

(tu/deftest-kb a-converse-reader-reads-the-genl-edges-its-placement-context-sees
  (doseq [edge-first? [true false]]
    (tu/with-terms [dog vocal hasVoice Rex Bark CxA CxB]
      (let [held? #(boolean (when-let [h (v/handle-of kb % CxA)] (v/in? kb h)))
            edge  #(v/assert kb (list 'genl vocal dog) CxB)]
        (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
        (when edge-first? (edge))
        (lazy-voice-world! kb CxA dog vocal hasVoice Rex Bark)
        (when-not edge-first? (edge))
        (is (held? (list vocal Rex)) (str "edge first: " edge-first?))))))

(tu/deftest-kb a-genl-edge-withholds-a-converse-reader-s-firing-in-either-order-until-it-departs
  (doseq [edge-first? [true false]]
    (tu/with-terms [dog vocal hasVoice Rex Bark CxA]
      (let [held? #(boolean (when-let [h (v/handle-of kb % CxA)] (v/in? kb h)))
            edge  #(v/assert kb (list 'genl vocal dog) CxA)
            e0    (when edge-first? (edge))]
        (lazy-voice-world! kb CxA dog vocal hasVoice Rex Bark)
        (let [e (or e0 (edge))]
          (is (false? (held? (list vocal Rex))) (str "edge first: " edge-first?))
          (v/retract! kb e)
          (is (true? (held? (list vocal Rex))) (str "retracted, edge first: " edge-first?)))))))

(tu/deftest-kb a-lazy-rule-s-exception-withholds-its-readers-firings-in-either-order
  (doseq [exception-first? [true false]]
    (tu/with-terms [dog deaf vocal hasVoice Rex Bark CxA]
      (let [held? #(boolean (when-let [h (v/handle-of kb % CxA)] (v/in? kb h)))
            lazy  (list 'set/lazyForwardRule (vr/rule-sentence [(list dog '?x)] (list hasVoice '?x Bark)))
            exc   #(v/assert kb (list 'exceptWhen (list deaf '?x) lazy) CxA)
            e0    (when exception-first? (exc))]
        (v/assert kb lazy CxA)
        (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list hasVoice '?x '?v)] (list vocal '?x)))
                  CxA)
        (v/assert kb (list dog Rex) CxA)
        (let [e (or e0 (exc))]
          (is (false? (held? (list vocal Rex))) (str "exception first: " exception-first?))
          (v/retract! kb e)
          (is (true? (held? (list vocal Rex))) (str "retracted, exception first: " exception-first?)))))))

(tu/deftest-kb a-batch-runs-each-owed-lazy-re-join-once-at-its-settle
  (tu/with-terms [cat feline noted ownerOf Ann Tom Kit Rex]
    (let [held?  #(boolean (when-let [h (v/handle-of kb % 'CxFam)] (v/in? kb h)))
          reader (vr/rule-sentence [(list ownerOf Ann '?x) (list feline '?x)] (list noted '?x))
          runs   (atom [])
          run    @#'chain/run-owed-rejoin
          member (with-redefs [chain/run-owed-rejoin
                               (fn [kb marker & more]
                                 (swap! runs conj (second marker))
                                 (apply run kb marker more))]
                   (v/with-deferred-settle kb
                     (v/assert kb (list 'set/lazyForwardRule
                                        (vr/rule-sentence [(list cat '?x)] (list feline '?x)))
                               'CxFam)
                     (v/assert kb (list 'set/forwardRule reader) 'CxFam)
                     (last (for [x [Tom Kit Rex]]
                             (do (v/assert kb (list ownerOf Ann x) 'CxFam)
                                 (v/assert kb (list cat x) 'CxFam))))))]
      (is (= 1 (count (filter #{(v/handle-of kb reader 'CxFam)} @runs))))
      (is (every? #(held? (list noted %)) [Tom Kit Rex]))
      (v/retract! kb member)
      (is (false? (held? (list noted Rex))))
      (is (held? (list noted Kit))))))

(tu/deftest-kb a-lazy-reader-s-re-join-proves-the-lazy-literal-from-the-arriving-membership
  (tu/with-terms [cat feline noted Tom]
    (let [held? #(boolean (when-let [h (v/handle-of kb % 'CxFam)] (v/in? kb h)))
          rows  (atom 0)
          solve @#'chain/solve-lazy]
      (v/assert kb (list 'set/lazyForwardRule (vr/rule-sentence [(list cat '?x)] (list feline '?x))) 'CxFam)
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list feline '?x)] (list noted '?x))) 'CxFam)
      (dotimes [_ 12] (v/assert kb (list cat (tu/tmp-ind "Kit")) 'CxFam))
      (with-redefs [chain/solve-lazy (fn [& args]
                                       (let [r (doall (apply solve args))] (swap! rows + (count r)) r))]
        (v/assert kb (list cat Tom) 'CxFam))
      (is (= 1 @rows))
      (is (held? (list noted Tom))))))

(defn- nonempty-reader!
  "A lazy-forward rule concluding `(inhabited ?c)` from `(nonempty ?c)` and a forward rule
  concluding `(noted ?c)` from it, in CxFam, `(listed ?c)` an antecedent of the lazy rule
  when `in-lazy?` and of the forward rule otherwise."
  [kb in-lazy? inhabited listed noted]
  (let [l (list listed '?c) i (list inhabited '?c)]
    (v/assert kb (list 'set/lazyForwardRule
                       (vr/rule-sentence (if in-lazy? [l (list 'nonempty '?c)] [(list 'nonempty '?c)]) i))
              'CxFam)
    (v/assert kb (list 'set/forwardRule (vr/rule-sentence (if in-lazy? [i] [l i]) (list noted '?c)))
              'CxFam)))

(tu/deftest-kb a-nonempty-lazy-reader-notes-a-type-whose-member-arrives-after-it
  (doseq [in-lazy? [true false]]
    (tu/with-terms [inhabited listed noted dog Fido]
      (let [held? #(boolean (when-let [h (v/handle-of kb % 'CxFam)] (v/in? kb h)))]
        (nonempty-reader! kb in-lazy? inhabited listed noted)
        (v/assert kb (list listed dog) 'CxFam)
        (is (false? (held? (list noted dog))) (str "listed in the lazy rule: " in-lazy?))
        (let [m (v/assert kb (list dog Fido) 'CxFam)]
          (is (true? (held? (list noted dog))) (str "listed in the lazy rule: " in-lazy?))
          (v/retract! kb m)
          (is (false? (held? (list noted dog))) (str "retracted, listed in the lazy rule: " in-lazy?)))))))

(tu/deftest-kb a-membership-re-joins-a-nonempty-lazy-rule-s-readers-over-the-types-it-moves
  (tu/with-terms [inhabited listed noted other Odd]
    (let [rows  (atom 0)
          solve @#'chain/solve-lazy]
      (nonempty-reader! kb true inhabited listed noted)
      (dotimes [_ 12]
        (let [t (tu/tmp-type "kind")]
          (v/assert kb (list listed t) 'CxFam)
          (v/assert kb (list t (tu/tmp-ind "Kit")) 'CxFam)))
      (with-redefs [chain/solve-lazy (fn [& args]
                                       (let [r (doall (apply solve args))] (swap! rows + (count r)) r))]
        (v/assert kb (list other Odd) 'CxFam))
      (is (zero? @rows)))))

(tu/deftest-kb a-wrapper-combination-the-record-cannot-hold-is-refused
  ;; The wrappers say how a rule runs (a direction, `set/defaultRule`) and what its head is
  ;; (a choice, a hard or a soft constraint).  A second answer to either, or a run mode on a
  ;; head a solve decides, has nowhere on the record to go; `check` predicts each refusal.
  (let [p (tu/tmp-pred) q (tu/tmp-pred)
        r (vr/rule-sentence [(list p '?x)] (list q '?x))]
    (doseq [[label s opts] [["two directions" (list 'set/forwardRule (list 'set/inertRule r)) nil]
                            ["a choice under a direction" (list 'set/forwardRule (list 'set/assumptionRule r)) nil]
                            ["a choice under a default" (list 'set/assumptionRule (list 'set/defaultRule r)) nil]
                            ["a constraint under a direction" (list 'set/hardConstraint (list 'set/backwardRule r)) nil]
                            ["a choice that is also a constraint" (list 'set/assumptionRule (list 'set/hardConstraint r)) nil]
                            ["a hard and a soft constraint" (list 'set/hardConstraint (list 'set/softConstraint r)) nil]
                            ["a :direction opt on a choice" (list 'set/assumptionRule r) {:direction :forward}]
                            ["behind an exceptWhen" (list 'exceptWhen (list p 'Nobody)
                                                          (list 'set/forwardRule (list 'set/assumptionRule r))) nil]]]
      (testing label
        (let [e (try (v/assert kb s 'CxFam opts) nil (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e) "refused")
          (is (contains? #{:not-well-formed :unknown-option} (:type (ex-data e))))
          (is (seq (v/check kb s 'CxFam opts)) "and check predicts it"))))
    (testing "each wrapper alone still stores"
      (doseq [s [(list 'set/forwardRule r) (list 'set/assumptionRule r)
                 (list 'set/hardConstraint r) (list 'set/defaultRule (list 'set/forwardRule r))]]
        (is (some? (v/assert kb s 'CxFam)) (pr-str s))))))
