;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.entry-point-and-report-test
  "One fact, one wording: a definitional check's **entry point** and its **retroactive reader**
  describe the same KB the same way.

  Several checks exist twice — once at the entry point as content arrives, once reading
  back over content admitted before the check could convict it — and the pair answers one question
  about one KB.  Neither half is wrong on its own, which is what makes the class expensive
  to debug: both messages are true statements about the same knowledge, so a reader who
  meets one and greps for the other finds nothing, and a reader who meets both concludes
  there are two problems.  The measured case is `arity`, where an inherited length reads as
  `fatherOf takes 2 arguments through parentOf` and the entry point that credited `fatherOf` with
  a declaration of its own sent an author looking for a sentence nobody wrote.

  So this is a **table** rather than one assertion each, on `vector-spelling-test`'s
  model: the defect is never in one half, it is in two halves disagreeing, and a table is
  what fails when the next pair is added on one side only.  The rows are
  [docs/taxonomy.md](../../docs/taxonomy.md)'s \"What each constraint does in each arrival
  order\" table, **including the cells that read \"nothing\"** — a check documented as
  having no retroactive half is a fact about the KB, and a sweep that quietly acquires one
  turns an open-world check into a closed-world one.

  What the two halves must agree on is the vocabulary a reader carries from one to the
  other: the **predicate or term blamed**, whether the constraint was **inherited** or
  declared outright, and **which stored sentex convicted**.  What they may differ on is
  said row by row, because the difference is real rather than sloppy: an entry point refuses one
  arriving sentence and names one reason, where a reader swept an extent and names a
  count.  A clash that names its members is stored at the entry point, so both halves of
  its row are the same nogood, a pair in which neither side is the newcomer."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

;; ---- reading the two halves ---------------------------------------------

(defn- standing-pairs
  "The pairs the last settle left standing — represented dilemmas and irreducible clashes
  alike.  One entry shape between them, and which reading a pair lands in is a question
  about the two sides' defeat classes rather than about the constraint that separated
  them."
  [kb]
  (concat (v/contradictions kb) (v/conflicts kb)))

(defn- entry-point
  "What a writer meets when `sentence` arrives last in a KB `setup` wrote.  A refusal is
  the first problem `check` names, plus `:against` — the **sentence** its
  `:opposing-handle` names.  A sentence the entry point stores instead answers the first
  standing pair the settle left, which is how a clash that names its members is met.

  Resolved to a sentence rather than compared as a handle, because the two halves of a
  pair are built in two KBs and a handle is allocation order.  The sentex convicted
  against is what the halves have to agree on; the integer naming it is not."
  ([setup sentence context] (entry-point setup sentence context {}))
  ([setup sentence context opts]
   (tu/with-cleared-kb [kb tu/fresh]
     (setup kb)
     (if-let [v (first (v/check kb sentence context opts))]
       (assoc v :against (:sentence (v/sentex kb (:opposing-handle v))))
       (do (v/assert kb sentence context opts)
           (first (standing-pairs kb)))))))

;; ---- arity: the pair with a binding to describe -------------------------
;;
;; A tuple of a length its binding breaks is stored in every order and held inert at
;; either strength, so the two halves are one reading: the same conflict, grounded on the
;; same binding, whichever of the tuple, the declaration and the edge arrived last
;; (docs/taxonomy.md, "Arity").

(defn- arity-reading
  "`[believed? [[kind sides grounds] …]]` for `fact` at `strength` in a KB `setup` wrote,
  the sides and grounds as sentences."
  [setup fact strength]
  (tu/with-cleared-kb [kb tu/fresh]
    (setup kb)
    (v/assert kb fact 'CxUniverse {:strength strength})
    (let [h (v/handle-of kb fact 'CxUniverse)]
      [(v/believed? kb h 'CxUniverse)
       (mapv (juxt :kind #(mapv :sentence (:sides %)) #(mapv :sentence (:grounds %)))
             (v/conflicts kb))])))

(deftest an-inert-tuple-reads-the-same-whichever-arrives-last
  (tu/with-terms [parentOf fatherOf A B C]
    (let [declaration (list 'binary_predicate parentOf)
          edge        (list 'genl fatherOf parentOf)]
      (doseq [{:keys [binding fact ingredients]}
              [{:binding     "declared of the predicate itself"
                :fact        (list parentOf A B C)
                :ingredients [declaration]}
               {:binding     "inherited, with the edge arriving last"
                :fact        (list fatherOf A B C)
                :ingredients [declaration edge]}
               {:binding     "inherited, with the length arriving last onto the super"
                :fact        (list fatherOf A B C)
                :ingredients [edge declaration]}]]
        (testing binding
          (let [late   (fn [kb] (doseq [s ingredients] (v/assert kb s 'CxUniverse)))
                first* (fn [kb] (v/assert kb fact 'CxUniverse {:strength :monotonic})
                         (doseq [s ingredients] (v/assert kb s 'CxUniverse)))]
            (is (= [false [[:arity [fact] [declaration]]]]
                   (arity-reading late fact :monotonic)
                   (arity-reading first* fact :monotonic)
                   (arity-reading late fact :default))
                "one conflict grounded on the declaration, in both orders and at either strength")))))))

;; ---- disjointness: every trigger, one nogood ----------------------------
;;
;; Four rows of the table share one retroactive reader (`settle/clash-nogoods`) and one
;; entry point (`checks/disjoint-problems`), and each row is a different sentence arriving last:
;; the separation itself, a metatype declaring its members pairwise separate, a term
;; joining such a metatype, a `genl` edge closing a separation over content already
;; stored, and a `genlCx` edge putting two contexts' memberships in one reader's sight.
;; The deciding half places the two memberships in sibling contexts that only CxBelow
;; sees together.  The on-demand `exposed-clashes` answer is `exposure_test`'s.

(deftest every-disjointness-trigger-stores-and-weighs-the-same-clash
  (tu/with-terms [dog_t cat_t pup_t meta_t alpha_t beta_t Rex CxLeft CxRight CxBelow]
    (let [ground (fn [& ts] (map #(list 'genl % 'thing) ts))
          rows
          [{:trigger 'disjoint
            :ground  (ground dog_t cat_t)
            :closing (list 'disjoint dog_t cat_t)
            :facts   [[(list dog_t Rex) 'CxUniverse] [(list cat_t Rex) 'CxUniverse]]}
           {:trigger 'disjoint_metatype
            :ground  (concat (ground meta_t alpha_t beta_t)
                             [(list meta_t alpha_t) (list meta_t beta_t)])
            :closing (list 'disjoint_metatype meta_t)
            :facts   [[(list alpha_t Rex) 'CxUniverse] [(list beta_t Rex) 'CxUniverse]]}
           {:trigger "a term joining a disjoint metatype"
            :ground  (concat (ground meta_t alpha_t beta_t)
                             [(list 'disjoint_metatype meta_t) (list meta_t alpha_t)])
            :closing (list meta_t beta_t)
            :facts   [[(list alpha_t Rex) 'CxUniverse] [(list beta_t Rex) 'CxUniverse]]}
           {:trigger 'genl
            :ground  (concat (ground dog_t cat_t pup_t) [(list 'disjoint dog_t cat_t)])
            :closing (list 'genl pup_t dog_t)
            :facts   [[(list cat_t Rex) 'CxUniverse] [(list pup_t Rex) 'CxUniverse]]}
           {:trigger 'genlCx
            :ground  (concat [(list 'genlCx CxLeft 'CxUniverse)
                              (list 'genlCx CxRight 'CxUniverse)]
                             (ground dog_t cat_t)
                             [(list 'disjoint dog_t cat_t)])
            :closing (list 'genlCx CxLeft CxRight)
            :facts   [[(list cat_t Rex) CxRight] [(list dog_t Rex) CxLeft]]
            ;; the report half's second edge into the context below both is the one that
            ;; completes the joint sight
            :report-below   [(list 'genlCx CxBelow CxRight)]
            :report-closing (list 'genlCx CxBelow CxLeft)}]]
      (doseq [{:keys [trigger ground closing facts report-below report-closing]} rows]
        (testing (str trigger " arriving last")
          (let [[[held held-ctx] [arriving arriving-ctx]] facts
                d (entry-point (fn [kb]
                                 (doseq [s (concat ground [closing])] (v/assert kb s 'CxUniverse))
                                 (v/assert kb held held-ctx))
                               arriving arriving-ctx)
                sight [(list 'genlCx CxLeft 'CxUniverse) (list 'genlCx CxRight 'CxUniverse)]
                below (or report-below
                          [(list 'genlCx CxBelow CxLeft) (list 'genlCx CxBelow CxRight)])
                c (tu/with-cleared-kb [kb tu/fresh]
                    (doseq [s (concat ground sight below)]
                      (v/assert kb s 'CxUniverse))
                    (v/assert kb held CxLeft)
                    (v/assert kb arriving CxRight)
                    (v/assert kb (or report-closing closing) 'CxUniverse)
                    (first (standing-pairs kb)))]
            (is (some? d) "the entry point stores the second membership and the pair is weighed")
            (is (some? c) "and the other order weighs the pair at CxBelow")
            (testing "both name the two memberships as the same kind, and neither adds one"
              (is (= :disjoint (:kind d) (:kind c)))
              (is (= #{held arriving}
                     (set (map :sentence (:sides d)))
                     (set (map :sentence (:sides c))))))))))))

;; ---- functional and asymmetric: a pair, not a message -------------------
;;
;; The retroactive half is a nogood re-derived through the entry point's own check, so
;; the table checks that it names the two sentences the entry point named.  Both rows put
;; the mark on a super-predicate, and either the mark or the `genl` edge arrives last.

(deftest a-descended-mark-weighs-the-same-pair-in-every-arrival-order
  (doseq [{:keys [kind mark edge held arriving strength]}
          (tu/with-terms [parentOf fatherOf Kid A B]
            [{:kind     :functional
              :mark     (list 'functional parentOf)
              :edge     (list 'genl fatherOf parentOf)
              :strength :default
              :held     (list fatherOf Kid 1980)
              :arriving (list fatherOf Kid 1990)}
             {:kind     :asymmetric
              :mark     (list 'asymmetric parentOf)
              :edge     (list 'genl fatherOf parentOf)
              :strength :monotonic
              :held     (list fatherOf A B)
              :arriving (list fatherOf B A)}])]
    (testing (name kind)
      (let [ingredient {:mark mark :edge edge}
            d (entry-point (fn [kb]
                             (doseq [s [edge mark]] (v/assert kb s 'CxUniverse))
                             (v/assert kb held 'CxUniverse {:strength strength}))
                           arriving 'CxUniverse {:strength strength})]
        (is (= kind (:kind d)) "the entry point stores the second fact and the pair is weighed")
        (is (= #{held arriving} (set (map :sentence (:sides d)))))
        (doseq [last-in [:mark :edge]]
          (testing (str "with the " (name last-in) " arriving last")
            (let [c (tu/with-cleared-kb [kb tu/fresh]
                      (doseq [k [:mark :edge] :when (not= k last-in)]
                        (v/assert kb (ingredient k) 'CxUniverse))
                      (doseq [s [held arriving]]
                        (v/assert kb s 'CxUniverse {:strength strength}))
                      (v/assert kb (ingredient last-in) 'CxUniverse)
                      (first (standing-pairs kb)))]
              (is (= kind (:kind c)) "the pair is weighed, and as the same kind")
              (is (= #{held arriving} (set (map :sentence (:sides c))))
                  "and it is the pair the fact-last order weighed"))))))))

(deftest a-cross-context-clash-is-weighed-as-the-same-pair
  ;; two facts each admissible where written, put in CxBelow's sight by two `genlCx`
  ;; edges, against the same two facts written into one context
  (doseq [{:keys [kind mark held arriving strength]}
          (tu/with-terms [parentOf Kid A B]
            [{:kind :functional :mark (list 'functional parentOf)
              :strength :default
              :held (list parentOf Kid 1980) :arriving (list parentOf Kid 1990)}
             {:kind :asymmetric :mark (list 'asymmetric parentOf)
              :strength :monotonic
              :held (list parentOf A B) :arriving (list parentOf B A)}])]
    (testing (name kind)
      (tu/with-terms [CxLeft CxRight CxBelow]
        (let [d (entry-point (fn [kb]
                               (v/assert kb mark 'CxUniverse)
                               (v/assert kb held 'CxUniverse {:strength strength}))
                             arriving 'CxUniverse {:strength strength})
              c (tu/with-cleared-kb [kb tu/fresh]
                  (doseq [s [(list 'genlCx CxLeft 'CxUniverse)
                             (list 'genlCx CxRight 'CxUniverse)
                             mark]]
                    (v/assert kb s 'CxUniverse))
                  (v/assert kb held CxLeft {:strength strength})
                  (v/assert kb arriving CxRight {:strength strength})
                  (v/assert kb (list 'genlCx CxBelow CxLeft) 'CxUniverse)
                  (v/assert kb (list 'genlCx CxBelow CxRight) 'CxUniverse)
                  (first (standing-pairs kb)))]
          (is (some? d) "the one-context order weighs the pair")
          (is (some? c) "and the split-context order weighs it at CxBelow")
          (is (= kind (:kind d) (:kind c)))
          (is (= #{held arriving}
                 (set (map :sentence (:sides d)))
                 (set (map :sentence (:sides c))))))))))

;; ---- the argument constraints' held facts --------------------------------
;;
;; `assert` of an argument constraint's last ingredient holds the content stored before it
;; inert, and the next claim is held alike (docs/argtypes.md, "An argument that fails its
;; declared type is held inert").  `try-assert` of a declaration arriving last refuses it
;; over the stored tuples it breaks (constraint_nogood_test); the test below covers `assert`.

(deftest the-argument-constraints-hold-what-came-before-and-what-follows
  ;; Forced to the constraint reading: the rows here convict a symbol argument, and with
  ;; the entailment on a symbol argument is minted rather than convicted
  ;; (docs/argtypes.md).  The entailment's own three arrival orders are held by
  ;; argtype_entail_test, which is where that reading answers the same question.
  (tu/without-entailing
   (tu/with-terms [person_t rock_t parentOf fatherOf eats grouped Rock Mary Pebble Bert Stone]
     (let [ground [(list 'genl person_t 'thing) (list 'genl rock_t 'thing)
                   (list 'disjoint person_t rock_t)
                   (list rock_t Rock) (list person_t Mary) (list rock_t Pebble)
                   (list 'variable_arity_predicate grouped)]
           rows
           [{:row     "arg, the declaration arriving last"
             :fact    (list parentOf Rock Mary)
             :closing (list 'arg parentOf 1 person_t)
             :next    (list parentOf Pebble Mary)
             :type    :arg-type}
            {:row     "genlArg, the declaration arriving last"
             :fact    (list parentOf Rock Mary)
             :closing (list 'genlArg parentOf 1 person_t)
             :next    (list parentOf Pebble Mary)
             :type    :arg-genl}
            ;; the conditional constraint has *three* ingredients: the fact and the
            ;; declaration are stored, and the membership arming the trigger arrives
            ;; afterwards
            {:row     "interArg, the trigger's type arriving last"
             :fact    (list eats Bert Pebble)
             :extra   [(list 'interArg eats 1 person_t 2 person_t)]
             :closing (list person_t Bert)
             :next    (list eats Bert Rock)
             :type    :inter-arg-type}
            ;; `quotedArg` takes the same reach: the mention twin convicts the *written*
            ;; term by the absence of a `genl` path, from `integer` to `string` here rather
            ;; than from an argument's type. Asserted so the cell is examined rather than
            ;; inherited from the three rows above.
            {:row     "quotedArg, the declaration arriving last"
             :fact    (list parentOf Mary 5)
             :closing (list 'quotedArg parentOf 2 'string)
             :next    (list parentOf Rock 7)
             :type    :quoted-arg-type}
            {:row     "quotedArg, the predicate edge arriving last"
             :fact    (list fatherOf Mary 5)
             :extra   [(list 'quotedArg parentOf 2 'string)]
             :closing (list 'genl fatherOf parentOf)
             :next    (list fatherOf Rock 7)
             :type    :quoted-arg-type}
            ;; one ingredient further out: the edge is admitted, and the fact it now convicts
            ;; is held inert
            {:row     "a predicate-level genl edge under an argument constraint"
             :fact    (list fatherOf Rock Mary)
             :extra   [(list 'arg parentOf 1 person_t)]
             :closing (list 'genl fatherOf parentOf)
             :next    (list fatherOf Pebble Mary)
             :type    :arg-type}
            ;; the covering forms type every position a sentence has, or every one from a
            ;; start, with `arg`'s per-argument conviction, so they take its reach
            ;; `args` read through the `argAndRest` twin core.txt's forward rule stores,
            ;; a rule this KB does not load
            {:row     "args, the declaration arriving last"
             :fact    (list parentOf Rock Mary)
             :extra   [tu/args-sugar-rule]
             :closing (list 'args parentOf person_t)
             :next    (list parentOf Pebble Mary)
             :type    :arg-type}
            {:row     "argAndRest, the declaration arriving last"
             :fact    (list parentOf Mary Rock)
             :closing (list 'argAndRest parentOf 2 person_t)
             :next    (list parentOf Mary Pebble)
             :type    :arg-type}
            ;; the homogeneity forms are `interArg` with one type in both roles, so each of
            ;; their three ingredients arriving after the fact is a cell: the declaration,
            ;; the trigger's type (Bert untyped until it arrives), and the target's (Stone)
            {:row     "interArgs, the declaration arriving last"
             :fact    (list grouped Mary Rock)
             :closing (list 'interArgs grouped person_t)
             :next    (list grouped Mary Pebble)
             :type    :inter-arg-type}
            {:row     "interArgs, the trigger's type arriving last"
             :fact    (list grouped Bert Rock)
             :extra   [(list 'interArgs grouped person_t)]
             :closing (list person_t Bert)
             :next    (list grouped Bert Pebble)
             :type    :inter-arg-type}
            {:row     "interArgs, the target's type arriving last"
             :fact    (list grouped Mary Stone)
             :extra   [(list 'interArgs grouped person_t)]
             :closing (list rock_t Stone)
             :next    (list grouped Mary Pebble)
             :type    :inter-arg-type}
            {:row     "interArgAndRest, the declaration arriving last"
             :fact    (list grouped Rock Mary Pebble)
             :closing (list 'interArgAndRest grouped 2 person_t)
             :next    (list grouped Rock Mary Rock)
             :type    :inter-arg-type}]]
       (doseq [{:keys [row fact extra closing next type]} rows]
         (testing row
           (tu/with-cleared-kb [kb tu/fresh]
             (doseq [s (concat ground [fact] extra [closing])]
               (v/assert kb s 'CxUniverse))
             (is (= [[fact type]]
                    (into [] (comp (filter #(= :inert-argument (:violation %)))
                                   (map (juxt :sentence (comp :type :detail))))
                          (v/violations kb)))
                 "the content admitted before the constraint existed is held and reported")
             (is (empty? (v/contradictions kb))
                 "and no pair is opened")
             (is (not (v/ask? kb fact 'CxUniverse)) "the stored fact is not believed")
             (is (= type (:type (tu/write-conviction kb next 'CxUniverse)))
                 "and the identical claim one line later is held alike"))))))))

(deftest a-stranded-declaration-is-a-census-finding-and-the-census-says-what-the-entry-point-says
  ;; The other documented absence, and the one whose retroactive half lives somewhere else
  ;; entirely.  `(arg fatherOf 3 person)` is admitted while nothing binds `fatherOf`'s
  ;; length; when a length arrives the declaration constrains a position the predicate
  ;; provably lacks, and the entry point refuses the identical sentence one line later.  It is not
  ;; refused retroactively — that would make the binding's arrival order decide — and not
  ;; filed in the ledger either, because a stranded declaration is inert and reads the same
  ;; an hour later, so there is no *newly* for a settle to report.  `kb-quality` names it,
  ;; and this is the row that keeps the census reading in the entry point's vocabulary.
  (tu/with-terms [parentOf fatherOf a_type]
    (tu/with-cleared-kb [kb tu/fresh]
      (doseq [s [(list 'genl a_type 'thing)
                 (list 'arg fatherOf 3 a_type)
                 (list 'binary_predicate parentOf)
                 (list 'genl fatherOf parentOf)]]
        (v/assert kb s 'CxUniverse))
      (is (empty? (v/violations kb)) "the settle files nothing")
      (let [e (first (:stranded (:declarations (v/kb-quality kb))))
            d (first (v/check kb (list 'arg fatherOf 3 a_type) 'CxUniverse))]
        (is (= :arg-position (:type d)) "the entry point refuses the identical sentence")
        (testing "and the census names the same predicate, position and binding"
          (is (= fatherOf (:predicate e) (:predicate d)))
          (is (= 3 (:position e) (:position d)))
          (is (= 2 (:arity e) (:arity d)))
          (is (= parentOf (:via e) (:via d))
              "the length came through the super, and both halves say so"))))))

(deftest two-declared-arities-across-one-edge-read-the-same-whichever-arrives-last
  ;; The pair is a nogood of the two declarations (a hard clash under CxUniverse, whose
  ;; forced-monotonic set stores both `:monotonic`), and the report is a fact about the pair rather than
  ;; about the arrival.
  (tu/with-terms [parentOf fatherOf]
    (let [sentence {:edge (list 'genl fatherOf parentOf)
                    :sub  (list 'arity fatherOf 3)}
          readings (into {}
                         (for [last-in [:edge :sub]]
                           [last-in
                            (tu/with-cleared-kb [kb tu/fresh]
                              (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
                              (doseq [k [:edge :sub] :when (not= k last-in)]
                                (v/assert kb (sentence k) 'CxUniverse))
                              (v/assert kb (sentence last-in) 'CxUniverse)
                              (mapv (juxt :kind #(into #{} (map :sentence) (:sides %)))
                                    (standing-pairs kb)))]))]
      (is (= (:edge readings) (:sub readings))
          "one pair, one report, whichever half of it arrived")
      (is (= [[:arity-descension #{(list 'arity fatherOf 3) (list 'arity parentOf 2)}]]
             (:edge readings))))))

;; ---- the wording spelled once -------------------------------------------

(deftest one-clause-words-an-arity-binding-for-every-reader-of-it
  ;; `checks/arity-binding-clause` is the wording the argument-position check carries, and
  ;; `kb-quality`'s stranded-declaration census carries that check's own message rather
  ;; than writing a second one.  A copy of a rule that says "is declared with" of a
  ;; declaration and "takes … through" of an inheritance is a chance for one binding to
  ;; acquire two descriptions, which is what this namespace is about.
  (tu/with-terms [parentOf fatherOf a_type]
    (let [inherited (checks/arity-binding-clause fatherOf parentOf 2)]
      (is (= (str "takes 2 arguments through " parentOf) inherited))
      (is (= "is declared with 2 arguments"
             (checks/arity-binding-clause parentOf parentOf 2)))
      (is (= "is declared with 1 argument"
             (checks/arity-binding-clause parentOf parentOf 1))
          "the plural agrees with the number, in one place rather than three")
      (testing "and the census, which carries the entry point's message unaltered"
        (tu/with-cleared-kb [kb tu/fresh]
          (doseq [s [(list 'genl a_type 'thing)
                     (list 'arg fatherOf 3 a_type)
                     (list 'binary_predicate parentOf)
                     (list 'genl fatherOf parentOf)]]
            (v/assert kb s 'CxUniverse))
          (is (str/includes? (v/quality-report (v/kb-quality kb)) inherited)))))))
