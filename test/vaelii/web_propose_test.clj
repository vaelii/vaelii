;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-propose-test
  "The proposal panel on a term page (`GET`/`POST /propose`), as pure request ->
  response — no server, and **no model**: every turn here runs against a scripted
  offline stub, so what is under test is the panel rather than what some model happened
  to say.

  Three invariants carry the route: proposing **writes nothing**, a runaway generation
  cannot hang the page (the turn always carries a token cap), and a backend that throws
  or is absent renders a message rather than a stack trace."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.llm.protocol :as proto]
            [vaelii.impl.llm.provider :as llm-provider]
            [vaelii.impl.llm.stub :as stub]
            [vaelii.impl.starter :as starter]
            [vaelii.impl.web :as web]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

(use-fixtures :once
  (fn [f]
    (let [kb (starter/load-into (tu/fresh))]
      (binding [tu/*kb* kb, *app* (web/app kb)] (f))
      (tu/clear-kb! kb))))
(use-fixtures :each (tu/neutral))

(defn- GET [uri qs]
  (*app* {:request-method :get :uri uri :query-string qs :params (or (:params {}) {})}))

(defn- POST
  ([params] (POST params nil))
  ([params headers]
   (*app* (cond-> {:request-method :post :uri "/propose" :scheme :http :params params}
            headers (assoc :headers headers)))))

(defn- scripted
  "A stub proposer the panel will run against, plus the stub itself so a test can read
  back what the panel actually asked it for."
  [& script]
  (let [p (stub/provider {:script (vec script)})]
    [{:kind :stub :provider p} p]))

(defn- a-page
  "A small term neighbourhood to propose about: a type under `animal`, one stored fact,
  and the context they live in."
  [kb]
  (let [[t ctx] [(tu/tmp-type "quokka") (tu/tmp-ctx "Marsupial")]]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext)
    (v/assert kb (list 'genl t 'animal) ctx)
    {:term t :ctx ctx}))

;; ---- the panel is on the page ------------------------------------------

(tu/deftest-kb the-term-page-carries-a-proposal-panel
  (let [{:keys [term]} (a-page kb)
        r (GET "/term" (str "q=" term))]
    (is (= 200 (:status r)))
    (testing "an instruction box that posts to /propose and swaps in place"
      (is (re-find #"id=\"propose\"" (:body r)))
      (is (re-find #"hx-post=\"/propose\"" (:body r)))
      (is (re-find #"hx-target=\"#propose-result\"" (:body r)))
      (is (re-find #"id=\"propose-result\"" (:body r))))
    (testing "and it names the backend it would talk to, without asking one anything"
      (is (re-find #"Propose knowledge" (:body r)))
      (is (re-find #"stub" (:body r))))))

(tu/deftest-kb the-panel-is-also-a-fragment-of-its-own
  (let [{:keys [term]} (a-page kb)
        r (GET "/propose" (str "q=" term))]
    (is (= 200 (:status r)))
    (is (re-find #"hx-post=\"/propose\"" (:body r)))
    (testing "a fragment, not a document"
      (is (not (re-find #"(?i)<!DOCTYPE" (:body r))))))
  (testing "an unreadable term asks nothing and renders nothing"
    (is (= "" (:body (GET "/propose" "q=%28%28%28"))))))

;; ---- a turn ------------------------------------------------------------

(tu/deftest-kb a-proposal-renders-its-lines-and-stores-none-of-them
  (let [{:keys [term ctx]} (a-page kb)
        sentence (list 'genl term 'bird)                    ; admissible, coins nothing
        [proposer _] (scripted {:assertions [sentence] :notes "guessing from the genus"})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"}))]
    (is (= 200 (:status r)))
    (testing "the sentence comes back on a line the KB would take as written"
      (is (re-find (re-pattern (str term)) (:body r)))
      (is (re-find #"class=\"p-line p-ok\"" (:body r)))
      (is (re-find #"✓" (:body r))))
    (testing "the tally says what it is and where it would land"
      (is (re-find #"1 proposed" (:body r)))
      (is (re-find #"1 ok" (:body r)))
      (is (re-find (re-pattern (str ctx)) (:body r))))
    (testing "the model's notes ride along"
      (is (re-find #"guessing from the genus" (:body r))))
    (testing "and **nothing was written** — a proposal is a proposal"
      (is (nil? (v/handle-of kb sentence ctx)))
      (is (empty? (v/sentexes-matching kb sentence ctx))))))

(tu/deftest-kb a-line-the-kb-would-refuse-carries-the-typed-reason-as-a-chip
  (let [{:keys [term ctx]} (a-page kb)
        good (list 'genl term 'bird)
        ;; non-ground and not a rule: `assert` refuses it, so `check-edit` does too
        bad  (list 'livesIn '?x 'Australia)
        ;; the same answer twice: the first rejection buys one repair turn, and the
        ;; second exhausts it, which is what makes the :invalid outcome deterministic
        [proposer _] (scripted {:assertions [good bad]} {:assertions [good bad]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "where does it live"}))]
    (is (= 200 (:status r)))
    (is (re-find #"class=\"p-line p-ok\"" (:body r)) "the good line still shows")
    (is (re-find #"class=\"p-line p-refused\"" (:body r)) "the bad one is marked, not dropped")
    (testing "the refusal is a word, not the checker's sentence"
      (is (re-find #"chip chip-refused\"[^>]*>.*?open</span>" (:body r))))
    (testing "and the message is behind the row's ?, not in the gutter"
      (is (re-find #"<details class=\"p-why\"" (:body r)))
      (is (re-find #"not ground" (:body r))))
    (testing "neither is stored"
      (is (nil? (v/handle-of kb good ctx)))
      (is (nil? (v/handle-of kb bad ctx))))))

;; ---- the chip gutter ----------------------------------------------------
;; Four independent things are worth knowing about a proposed line, and prose buries
;; all of them.  Each is a glyph and one word; the explanation is one `?` away.

(tu/deftest-kb a-correction-shows-the-original-superseded-by-its-rewrite
  ;; filed where the shipped schema states it: the definitional checks are
  ;; context-scoped, so which constraints are visible is part of what a line is judged on
  (let [_ (a-page kb)
        ;; the dominant remaining error class: the right claim about the wrong thing —
        ;; stated of the type symbol rather than of its instances
        [proposer _] (scripted {:assertions ['(mortal penguin)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" "penguin" "ctx" "OrganismContext" "message" "what is true of it"}))]
    (is (= 200 (:status r)))
    (testing "the original is struck through rather than hidden — the author chooses"
      (is (re-find #"class=\"p-was\"" (:body r)))
      (is (re-find #"mortal" (:body r))))
    (testing "the rewrite follows it"
      (is (re-find #"class=\"p-to\"" (:body r)))
      (is (re-find #"defaultRule" (:body r))))
    (testing "the chip names the kind of restatement, in one word"
      (is (re-find #"chip chip-correction\"[^>]*>.*?shape</span>" (:body r))))
    (testing "and the other defensible shape is flagged without spelling it out inline"
      (is (re-find #"class=\"p-alts\">\[genl\]" (:body r))))))

(tu/deftest-kb coined-vocabulary-is-impossible-to-miss
  (let [{:keys [term ctx]} (a-page kb)]
    (tu/with-terms [waddles]
      (let [[proposer _] (scripted {:assertions [(list 'implies (list term '?x)
                                                       (list waddles '?x))]})
            r (binding [web/*proposer* proposer]
                (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "how does it move"}))]
        (is (re-find #"class=\"p-line p-coins\"" (:body r)))
        (is (re-find #"chip chip-coins\"[^>]*>.*?property</span>" (:body r))
            "a one-place property and an n-place relation are different risks")
        (is (re-find (re-pattern (str "title=\"" waddles " takes 1 argument")) (:body r)))))))

(tu/deftest-kb an-undecidable-rewrite-says-so-rather-than-choosing
  (let [_ (a-page kb)
        ;; both of `partOf`'s positions want the same type, so the direction of the lift
        ;; is not inferable — that is a decision handed back, not a detail
        [proposer _] (scripted {:assertions ['(partOf penguin wing)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" "penguin" "ctx" "OrganismContext" "message" "what is it made of"}))]
    (is (re-find #"class=\"p-line p-uncertain\"" (:body r)))
    (is (re-find #"chip chip-uncertain\"[^>]*>.*?direction</span>" (:body r)))))

(tu/deftest-kb the-gutter-explains-its-own-glyphs
  (let [{:keys [term ctx]} (a-page kb)
        [proposer _] (scripted {:assertions [(list 'genl term 'bird)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"}))]
    (is (re-find #"class=\"legend\"" (:body r)))
    (doseq [word ["ok" "coins" "uncertain" "refused"]]
      (is (str/includes? (:body r) (str "</span> " word "</span>"))
          (str "the legend names " word)))))

;; ---- choosing between shapes -------------------------------------------
;; `correct` refuses to pick between the definitional and the defeasible reading, so the
;; reader picks — and it has to cost one key, because it is the commonest decision in a
;; review pass.

(defn- POST-to
  ([uri params] (POST-to uri params nil))
  ([uri params headers]
   (*app* (cond-> {:request-method :post :uri uri :scheme :http :params params}
            headers (assoc :headers headers)))))

(tu/deftest-kb every-shape-is-numbered-and-the-rewrite-leads
  (let [_ (a-page kb)
        [proposer _] (scripted {:assertions ['(mortal penguin)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" "penguin" "ctx" "OrganismContext" "message" "what is true of it"}))]
    (testing "three shapes: what the model wrote, the rewrite, and the definitional reading"
      (is (re-find #"data-n=\"1\"" (:body r)))
      (is (re-find #"data-n=\"2\"" (:body r)))
      (is (re-find #"data-n=\"3\"" (:body r)))
      (is (not (re-find #"data-n=\"4\"" (:body r)))))
    (testing "the rewrite is the one selected, so the common case needs no keystroke"
      (is (re-find #"aria-pressed=\"true\" class=\"p-opt on\" data-n=\"2\"" (:body r))))
    (testing "each shape carries the sentence it would store, so a hover says what it is"
      (is (str/includes? (:body r) "title=\"(genl penguin mortal)\"")))
    (testing "and the row posts back the original, never the shape it is showing"
      (is (str/includes? (:body r) "name=\"from\" type=\"hidden\" value=\"(mortal penguin)\"")))))

(tu/deftest-kb choosing-a-shape-re-checks-the-sentence-that-would-be-stored
  (let [_ (a-page kb)
        row (fn [n] (:body (POST-to "/propose/line"
                                    {"from" "(mortal penguin)" "ctx" "OrganismContext"
                                     "i" "0" "n" n})))]
    (testing "shape 3 is the genl edge, and the line to store follows the choice"
      (let [b (row "3")]
        (is (re-find #"aria-pressed=\"true\" class=\"p-opt on\" data-n=\"3\"" b))
        (is (str/includes? b "value=\"[(genl penguin mortal) OrganismContext]\""))))
    (testing "shape 1 is the sentence as written, and then nothing is superseded"
      (let [b (row "1")]
        (is (str/includes? b "value=\"[(mortal penguin) OrganismContext]\""))
        (is (not (re-find #"class=\"p-was\"" b)))))
    (testing "a number the line does not have is clamped, not an error — it is a keystroke"
      (is (re-find #"data-n=\"3\"" (row "9"))))
    (testing "the re-checked chips are of the chosen shape"
      ;; `(genl penguin mortal)` is admissible where `(mortal penguin)` is corrected, so
      ;; the correction chip stays (it is why the line was restated) and no refusal appears
      (is (re-find #"class=\"p-line p-ok\"" (row "3")))
      (is (not (re-find #"chip-refused" (row "3")))))
    (testing "and re-rendering a row stores nothing"
      (is (nil? (v/handle-of kb '(genl penguin mortal) 'OrganismContext))))))

(tu/deftest-kb a-shape-choice-is-re-derived-not-trusted
  ;; the request carries the original and a number; the sentence it renders comes from
  ;; `correct` reading the KB, so nothing arbitrary can be posted into the row
  (let [b (:body (POST-to "/propose/line" {"from" "(mortal penguin)" "ctx" "OrganismContext"
                                           "i" "0" "n" "2"}))]
    (is (str/includes? b "defaultRule"))
    (is (not (str/includes? b "(evil penguin)")))))

;; ---- accepting, and the one write --------------------------------------

(tu/deftest-kb accepted-lines-are-stored-in-one-batch
  (tu/with-terms [quokka QuokkaContext]
    (v/assert kb (list 'genlContext QuokkaContext 'WellContext) 'UniverseContext)
    (v/assert kb (list 'genl quokka 'animal) QuokkaContext)
    (let [a (pr-str [(list 'genl quokka 'mammal) QuokkaContext])
          b (pr-str [(list 'genl quokka 'herbivore) QuokkaContext])
          before (count (tu/justification-ids kb))
          r (POST-to "/propose/apply" {"line" [a b]})]
      (is (= 200 (:status r)))
      (is (re-find #"Stored 2 lines" (:body r)))
      (testing "both are premises now"
        (is (seq (v/sentexes-matching kb (list 'genl quokka 'mammal) QuokkaContext)))
        (is (seq (v/sentexes-matching kb (list 'genl quokka 'herbivore) QuokkaContext))))
      (testing "and the reader can reach them"
        (is (re-find #"/sentex/" (:body r))))
      (is (>= (count (tu/justification-ids kb)) before)))))

(tu/deftest-kb a-single-accepted-line-arrives-as-a-bare-string
  ;; one accepted row means one `line` param, and ring hands that back unwrapped
  (tu/with-terms [wombat WombatContext]
    (v/assert kb (list 'genlContext WombatContext 'WellContext) 'UniverseContext)
    (let [r (POST-to "/propose/apply"
                     {"line" (pr-str [(list 'genl wombat 'animal) WombatContext])})]
      (is (re-find #"Stored 1 line" (:body r)))
      (is (seq (v/sentexes-matching kb (list 'genl wombat 'animal) WombatContext))))))

(tu/deftest-kb accepting-nothing-writes-nothing
  (let [before (tu/sentex-ids kb)
        r (POST-to "/propose/apply" {})]
    (is (= 200 (:status r)))
    (is (re-find #"Nothing was accepted" (:body r)))
    (is (= before (tu/sentex-ids kb)))))

(tu/deftest-kb a-batch-with-one-bad-line-stores-none-of-it
  (tu/with-terms [numbat NumbatContext]
    (v/assert kb (list 'genlContext NumbatContext 'WellContext) 'UniverseContext)
    (let [good (pr-str [(list 'genl numbat 'animal) NumbatContext])
          bad  (pr-str [(list 'genl numbat 'Muffet) NumbatContext])
          r (POST-to "/propose/apply" {"line" [good bad]})]
      (is (re-find #"Nothing was stored" (:body r)))
      (is (re-find #"not-well-formed" (:body r)))
      (testing "including the line that was fine — a half-applied review is nobody's answer"
        (is (empty? (v/sentexes-matching kb (list 'genl numbat 'animal) NumbatContext)))))))

(tu/deftest-kb a-line-the-correction-can-only-report-cannot-be-stored
  ;; `partOf` is declared binary; a third argument is a surplus no rule can pick, so
  ;; `correct/apply-correction` answers nil and there is nothing to accept
  (let [_ (a-page kb)
        [proposer _] (scripted {:assertions ['(partOf penguin wing feather)]}
                               {:assertions ['(partOf penguin wing feather)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" "penguin" "ctx" "OrganismContext" "message" "what is it made of"}))]
    (testing "the row offers no accept at all"
      (is (re-find #"report only|nothing to store" (:body r)))
      (is (not (re-find #"data-accept" (:body r))))))
  (testing "and the server refuses it even when the field is posted anyway — a check that
            only runs in the browser is not a check"
    (let [r (POST-to "/propose/apply"
                     {"line" (pr-str ['(partOf penguin wing feather) 'OrganismContext])})]
      (is (re-find #"Nothing was stored" (:body r)))
      (is (empty? (v/sentexes-matching kb '(partOf penguin wing feather) 'OrganismContext))))))

(tu/deftest-kb the-review-list-is-a-keyboard-grid
  (let [{:keys [term ctx]} (a-page kb)
        [proposer _] (scripted {:assertions [(list 'genl term 'bird)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"}))]
    (testing "a grid with a roving tabindex, so Tab reaches it once and keys move inside"
      (is (re-find #"class=\"propose-lines[^\"]*\" role=\"grid\"" (:body r)))
      (is (re-find #"role=\"row\" tabindex=\"0\"" (:body r))))
    (testing "the keys are named where a reader will look for them"
      (is (re-find #"<kbd>j</kbd>" (:body r)))
      (is (re-find #"<kbd>a</kbd>" (:body r)))
      (is (re-find #"<kbd>1</kbd>" (:body r))))
    (testing "and accepting is a disabled field, so the browser assembles the payload"
      (is (re-find #"disabled=\"disabled\" name=\"line\"" (:body r))))))

;; ---- what accepting would do (POST /propose/preview) -------------------
;; The panel's second question.  The chips say whether a line would be *admitted*; this
;; says what the accepted set would *mean*, and it is the question a line can pass on
;; its own and fail together.  Every test here also asserts the KB did not move: the
;; whole point of running a preview on every keystroke-ish change is that it is free to
;; be wrong about, and a preview that stored something would not be.

(defn- preview-body
  "POST the accepted lines and hand back the rendered panel."
  [lines]
  (:body (POST-to "/propose/preview" {"line" lines})))

(tu/deftest-kb accepting-a-line-a-rule-fires-on-shows-the-conclusion
  (tu/with-terms [dog friendly Rex DogContext]
    (v/assert kb (list 'genlContext DogContext 'WellContext) 'UniverseContext)
    (v/assert kb (list 'set/forwardRule (list 'implies (list dog '?x) (list friendly '?x)))
              DogContext)
    (let [before (tu/sentex-ids kb)
          body   (preview-body (pr-str [(list dog Rex) DogContext]))]
      (testing "the line and what it would derive, counted and grouped"
        (is (re-find #"Consequences of accepting 1 line" body))
        (is (re-find #"2 newly believed" body))
        (is (re-find (re-pattern (str friendly)) body)))
      (testing "the derived line names the rule that would conclude it"
        (is (re-find #"by </span>" body))
        (is (re-find #"implies" body)))
      (testing "collapsed until asked for"
        (is (re-find #"<details class=\"p-cons p-cons-add\">" body)))
      (is (= before (tu/sentex-ids kb)) "a preview stored something"))))

(tu/deftest-kb accepting-content-that-withdraws-a-belief-says-so
  ;; `exceptWhen` is where a withdrawal actually comes from: the fact that makes the
  ;; exception hold blocks the rule, and the conclusion resting on it goes.
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (v/assert kb (list 'genlContext BirdContext 'WellContext) 'UniverseContext)
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule
                             (list 'implies (list bird '?b) (list flies '?b))))
              BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (let [h      (v/handle-of kb (list flies Opus) BirdContext)
          before (tu/sentex-ids kb)
          body   (preview-body (pr-str [(list penguin Opus) BirdContext]))]
      (is (some? h) "the conclusion has to exist for its withdrawal to be visible")
      (testing "the withdrawal is reported, with its reason and a link to why"
        (is (re-find #"1 no longer believed" body))
        (is (re-find (re-pattern (str flies)) body))
        (is (re-find #"tag-unsupported" body))
        (is (re-find (re-pattern (str "/why/" h)) body)))
      (testing "and it is still believed — the withdrawal was hypothetical"
        (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext))))
      (is (= before (tu/sentex-ids kb))))))

(tu/deftest-kb accepting-the-negation-of-a-default-reports-the-dilemma-it-opens
  ;; A default against a default withdraws nothing — both sides stay believed and the
  ;; pair is represented (docs/nmtms.md).  Reporting only the two diff halves would tell
  ;; a reader the line simply arrived, which is the one thing that did not happen.
  (tu/with-terms [flies Tweety BirdContext]
    (v/assert kb (list 'genlContext BirdContext 'WellContext) 'UniverseContext)
    (v/assert kb (list flies Tweety) BirdContext)
    (let [before (tu/sentex-ids kb)
          body   (preview-body (pr-str [(list 'not (list flies Tweety)) BirdContext]))]
      (is (re-find #"1 now contested" body))
      (is (re-find #"p-cons-tie" body))
      (testing "opened, because it is the answer that would otherwise be silence"
        (is (re-find #"class=\"p-cons p-cons-tie\" open=\"open\"" body)))
      (is (= before (tu/sentex-ids kb))))))

(tu/deftest-kb two-lines-each-admissible-alone-are-refused-together
  ;; the case a per-line check cannot see, and the reason the preview is over the
  ;; accepted *set* rather than over each row
  (tu/with-terms [fish mammal Willy SeaContext]
    (v/assert kb (list 'genlContext SeaContext 'WellContext) 'UniverseContext)
    (v/assert kb (list 'disjoint fish mammal) SeaContext)
    (let [before (tu/sentex-ids kb)
          body   (preview-body [(pr-str [(list fish Willy) SeaContext])
                                (pr-str [(list mammal Willy) SeaContext])])]
      (testing "the loud group, open, naming the line by its position"
        (is (re-find #"class=\"p-cons p-cons-bad\" open=\"open\"" body))
        (is (re-find #"1 refused" body))
        (is (re-find #"disjoint" body))
        (is (re-find #"line 2" body)))
      (is (= before (tu/sentex-ids kb))))))

(tu/deftest-kb a-batch-that-follows-from-nothing-says-nothing-follows
  (tu/with-terms [quoll QuollContext]
    (v/assert kb (list 'genlContext QuollContext 'WellContext) 'UniverseContext)
    (v/assert kb (list 'genl quoll 'animal) QuollContext)
    (let [body (preview-body (pr-str [(list 'genl quoll 'animal) QuollContext]))]
      (is (re-find #"Nothing follows" body)
          "re-asserting what is already believed adds no belief and withdraws none"))))

(tu/deftest-kb previewing-nothing-asks-for-a-line-rather-than-erroring
  (let [r (POST-to "/propose/preview" {})]
    (is (= 200 (:status r)))
    (is (re-find #"Accept a line" (:body r)))))

(tu/deftest-kb a-report-only-line-is-left-out-of-the-preview
  ;; the commit refuses it, so previewing it would promise a consequence the button
  ;; will not deliver
  (let [body (preview-body (pr-str ['(partOf penguin wing feather) 'OrganismContext]))]
    (is (re-find #"report-only" body))
    (is (re-find #"Nothing left to preview" body))))

(tu/deftest-kb the-review-form-asks-for-the-preview-and-debounces-it
  (let [{:keys [term ctx]} (a-page kb)
        [proposer _] (scripted {:assertions [(list 'genl term 'bird)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"}))
        body (:body r)]
    (testing "the panel is on the review form, fed by the same fields the commit posts"
      (is (re-find #"id=\"p-preview\"" body))
      (is (re-find #"hx-post=\"/propose/preview\"" body))
      (is (re-find #"hx-include=\"\.propose-apply\"" body)))
    (testing "recomputed on the accepted set, not per keystroke"
      (is (re-find #"hx-trigger=\"accepted-changed from:body delay:400ms\"" body)))
    (testing "and it starts empty rather than guessing"
      (is (re-find #"Accept a line to see what it would do" body)))))

(deftest the-review-script-announces-the-accepted-set-once-per-change
  (let [js (slurp "resources/public/select.js")]
    (testing "the event the panel's hx-trigger listens for"
      (is (str/includes? js "accepted-changed")))
    (testing "keyed on the lines, so re-choosing a shape on an accepted row counts"
      (is (str/includes? js "input[name='line']")))
    (testing "and not re-fired when nothing about the accepted set moved"
      (is (str/includes? js "if (key === lastAccepted) return;")))))

(deftest a-bounded-preview-says-so-rather-than-implying-completeness
  ;; the renderer directly: making a real batch cascade past the cap costs more than the
  ;; claim is worth, and what is under test here is that the panel *reports* the flag
  ;; `preview` sets (`preview_test` pins that it sets it)
  (let [panel (fn [result]
                (str (#'web/consequence-panel {:kb tu/*kb*} 1 result)))
        capped (panel {:believed-added [{:sentence '(dog Muffet) :context 'WellContext}]
                       :believed-removed [] :refused [] :violations []
                       :contradictions [] :bounded? true})
        whole  (panel {:believed-added [{:sentence '(dog Muffet) :context 'WellContext}]
                       :believed-removed [] :refused [] :violations []
                       :contradictions [] :bounded? false})]
    (is (str/includes? capped "cut short"))
    (is (str/includes? capped (str @#'web/preview-max-results))
        "a reader told the answer is partial should be told where it stopped")
    (is (not (str/includes? whole "cut short")))
    (testing "and either way, that nothing was stored"
      (is (str/includes? whole "Nothing here is stored")))))

(tu/deftest-kb the-preview-is-origin-checked-like-every-other-post
  (let [hdrs {"origin" "http://evil.example" "host" "localhost:3000"}]
    (is (= 403 (:status (POST-to "/propose/preview"
                                 {"line" (pr-str ['(genl dog animal) 'WellContext])}
                                 hdrs))))))

(tu/deftest-kb the-writes-are-origin-checked-like-every-other
  (let [hdrs {"origin" "http://evil.example" "host" "localhost:3000"}]
    (tu/with-terms [bilby BilbyContext]
      (v/assert kb (list 'genlContext BilbyContext 'WellContext) 'UniverseContext)
      (let [line (pr-str [(list 'genl bilby 'animal) BilbyContext])]
        (is (= 403 (:status (POST-to "/propose/apply" {"line" line} hdrs))))
        (is (empty? (v/sentexes-matching kb (list 'genl bilby 'animal) BilbyContext))
            "a cross-origin commit writes nothing")
        (is (= 403 (:status (POST-to "/propose/line"
                                     {"from" "(mortal penguin)" "ctx" "OrganismContext"
                                      "i" "0" "n" "2"} hdrs))))))))

;; ---- no problem type reaches the gutter as an exception string ----------

(def ^:private declared-problem-types
  "Every `:type` the checking namespaces attach to a problem, read out of the source
  rather than listed by hand — a check that grows a new type is caught here whether or
  not anyone remembers this test.

  The lookahead drops `(dissoc p :type :sentence)`, where the two keywords are arguments
  rather than a key and its value — the name must run to its end (not a name character)
  and that end must not be a closing paren."
  (delay
    (->> ["src/vaelii/core.clj" "src/vaelii/impl/checks.clj" "src/vaelii/impl/wff.clj"
          "src/vaelii/impl/naming.clj" "src/vaelii/impl/rules.clj" "src/vaelii/impl/sentex.clj"]
         (mapcat #(re-seq #":type :([a-z][a-z-]*)(?![-a-z)\]])" (slurp %)))
         (map second)
         (map keyword)
         set)))

(deftest every-check-problem-type-reaches-a-chip-and-none-is-a-raw-message
  (let [word @#'web/problem-chip-word]
    (is (seq @declared-problem-types) "the scan found the checking namespaces")
    (testing "every type a check can attach has a curated word — a keyword name is a
              fallback, not a design"
      (doseq [t @declared-problem-types]
        (let [w (@#'web/problem-word t)]
          (is (string? w) (str t " has no chip word"))
          (is (<= (count (str w)) 14) (str t " is a word, not a message: " (pr-str w))))))
    (testing "and a type nobody has written yet still renders as a chip, never as prose"
      (let [w (word :wildly-new)]
        (is (= "wildly-new" w))
        (is (not (re-find #"[\s.,;:()]" w)))))))

(tu/deftest-kb an-answer-that-cannot-be-read-is-reported-not-thrown
  (let [{:keys [term ctx]} (a-page kb)
        ;; a real model writing prose instead of assertions — the failure this reports,
        ;; so the kind is a real backend even though a scripted stub plays it
        [{:keys [provider]} _] (scripted "I would rather write an essay about quokkas."
                                         "On reflection, a sonnet about quokkas.")
        r (binding [web/*proposer* {:kind :ollama :provider provider}]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "anything"}))]
    (is (= 200 (:status r)))
    (is (re-find #"could not be read" (:body r)))
    (testing "under it, what the model said **last** — the first answer bought a repair
              turn, and the reader is owed the one that ended the exchange"
      (is (re-find #"sonnet about quokkas" (:body r)))
      (is (not (re-find #"essay about quokkas" (:body r)))))))

(tu/deftest-kb with-no-provider-configured-the-stub-answers-and-nothing-errors
  ;; no *proposer* binding at all: the route resolves its own, which with nothing
  ;; configured is the offline stub — the state a machine with no model is in.
  ;;
  ;; `configured` is redefined rather than left to the machine, and that is what keeps
  ;; this test in `:default`.  The route resolves through `llm-provider/active-kind`,
  ;; which reads `VAELII_LLM_PROVIDER` / `-Dvaelii.llm.provider` — so on a machine that
  ;; names a backend this would probe the host and run a real generation turn, with no
  ;; `^:llm` mark and no `tu/live-llm?` gate to stop it.  Nothing else in this namespace
  ;; leaves `*proposer*` unbound; this one must, since the resolution *is* the subject.
  (with-redefs [llm-provider/configured (constantly nil)]
    (let [{:keys [term ctx]} (a-page kb)
          r (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "flesh this out"})]
      (is (= 200 (:status r)))
      (is (re-find #"0 proposed" (:body r)))
      (testing "and it says *why* it proposed nothing — a machine with no model configured
                is not a parse failure, and sending a reader after one would waste their day"
        (is (re-find #"No model is configured" (:body r)))
        (is (re-find #"VAELII_LLM_PROVIDER" (:body r))))
      (is (empty? (v/find-sentexes kb 'herbivore)) "and it wrote nothing"))))

(tu/deftest-kb a-backend-that-throws-renders-a-message-not-a-stack-trace
  (let [{:keys [term ctx]} (a-page kb)
        boom (reify proto/Provider
               (complete [_ _] (throw (ex-info "host went away" {})))
               (stream [_ _ _] (throw (ex-info "host went away" {}))))
        r (binding [web/*proposer* {:kind :ollama :provider boom}]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "anything"}))]
    (is (= 200 (:status r)))
    (is (re-find #"The turn failed" (:body r)))
    (is (re-find #"host went away" (:body r)))
    (is (not (re-find #"clojure\.lang" (:body r))))))

;; ---- the runaway guard --------------------------------------------------
;; Two of eight models measured degenerate into runaway generation — one wrote 8138
;; lines over 474 seconds.  A wall-clock timeout is no answer (the host keeps
;; generating), so the bound is on tokens and it rides on every turn the panel sends.

(tu/deftest-kb every-turn-carries-a-token-cap
  (let [{:keys [term ctx]} (a-page kb)
        [proposer p] (scripted {:assertions [(list 'genl term 'animal)]})
        _ (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "anything"}))
        requests (stub/requests p)]
    (is (seq requests) "the panel actually ran a turn")
    (doseq [req requests]
      (is (number? (:max-tokens req)) "a turn with no cap is a turn that can run away")
      (is (<= (:max-tokens req) 4096))
      (testing "and the window it is sized against is bounded too"
        (is (number? (:num-ctx req)))))))

;; ---- the origin check ---------------------------------------------------
;; The turn writes nothing, but it spends a model (and on a local host, a GPU), so a
;; page on another site must not be able to make this browser run one.

(tu/deftest-kb a-cross-origin-proposal-is-refused
  (let [{:keys [term ctx]} (a-page kb)
        [proposer p] (scripted {:assertions [(list 'genl term 'animal)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "anything"}
              {"origin" "http://evil.example" "host" "localhost:3000"}))]
    (is (= 403 (:status r)))
    (is (str/includes? (:body r) "cross-origin"))
    (is (empty? (stub/requests p)) "and no model was spent")))

(tu/deftest-kb a-same-origin-proposal-runs
  (let [{:keys [term ctx]} (a-page kb)
        [proposer p] (scripted {:assertions [(list 'genl term 'animal)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "anything"}
              {"origin" "http://localhost:3000" "host" "localhost:3000"}))]
    (is (= 200 (:status r)))
    (is (seq (stub/requests p)))))

;; ---- disclosure: one row at three densities -----------------------------
;;
;; The level belongs to the **view**, not to a preferences panel: a reader working
;; through fifty lines wants a gutter, a reader meeting their first refusal wants the
;; sentence spelled out, and the same reader is both within one session.  So what these
;; hold is that the three are one renderer configured three ways, that changing density
;; costs no second turn, and that each level actually withholds what it claims to.

(tu/deftest-kb a-term-page-opens-at-working-and-offers-the-other-two
  (let [{:keys [term ctx]} (a-page kb)
        [proposer _] (scripted {:assertions [(list 'genl term 'bird)]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"}))]
    (is (re-find #"class=\"p-level on\"[^>]*>Working" (:body r))
        "a term page is where vocabulary is worked through")
    (testing "and the switch is on the page, not in a settings panel"
      (is (re-find #">Guided<" (:body r)))
      (is (re-find #">Dense<" (:body r))))))

(defn- visible
  "The text a reader actually sees: markup stripped, so an assertion about what a level
  withholds is not satisfied — or defeated — by a hidden field's value. The row still has
  to post its context back; that is machinery, not something rendered."
  [body]
  (-> body (str/replace #"<[^>]*>" " ") (str/replace #"\s+" " ")))

(tu/deftest-kb each-level-withholds-exactly-what-it-says-it-does
  (let [{:keys [term ctx]} (a-page kb)
        ;; a line the KB refuses, so there is a reason to render or withhold
        bad  (list 'lives_in term 'Australia)
        run  (fn [lvl]
               (let [[proposer _] (scripted {:assertions [bad]} {:assertions [bad]})]
                 (:body (binding [web/*proposer* proposer]
                          (POST {"q" (pr-str term) "ctx" (pr-str ctx)
                                 "message" "where" "level" lvl})))))
        guided (run "guided") working (run "working") dense (run "dense")]
    (testing "dense renders no sentence of explanation unasked — absent, not folded"
      (is (not (re-find #"p-why" dense)))
      (is (re-find #"p-glyph" dense) "the gutter is still there"))
    (testing "working folds the reason behind the ?"
      (is (re-find #"p-why" working))
      (is (not (re-find #"p-said" working))))
    (testing "guided spells it out instead of folding it"
      (is (re-find #"p-said" guided)))
    (testing "guided shows no context name and no engine vocabulary"
      ;; the placement is still what it was; it is not what this reader is deciding
      (is (not (re-find (re-pattern (str ctx)) (visible guided))))
      (is (not (re-find #"(?i)sentex" (visible guided)))))
    (testing "the other levels do name the context, because their reader has that word"
      (is (re-find (re-pattern (str ctx)) (visible working))))))

(tu/deftest-kb changing-the-level-re-reads-the-proposal-and-asks-no-model
  (let [{:keys [term ctx]} (a-page kb)
        sentence (list 'genl term 'bird)
        [proposer stub] (scripted {:assertions [sentence]})
        _ (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"}))
        asked-once (count (stub/requests stub))
        ;; the switch posts the list's own originals back — the same fields the row
        ;; carries — and gets the same proposal at another density
        r (binding [web/*proposer* proposer]
            (POST-to "/propose/level" {"from" (pr-str sentence) "ctx" (pr-str ctx)
                                       "level" "guided"} nil))]
    (is (= 200 (:status r)))
    (is (re-find (re-pattern (str term)) (:body r)) "the same line came back")
    (is (re-find #"class=\"p-level on\"[^>]*>Guided" (:body r)) "at the level asked for")
    (is (= asked-once (count (stub/requests stub)))
        "and the model was not asked a second time")))

(tu/deftest-kb the-guided-level-says-what-a-line-would-mean
  (let [{:keys [term ctx]} (a-page kb)
        ;; `genl` is fully documented, so the gloss is composed from the KB's own comment
        sentence (list 'genl term 'bird)
        [proposer _] (scripted {:assertions [sentence]})
        r (binding [web/*proposer* proposer]
            (POST {"q" (pr-str term) "ctx" (pr-str ctx) "message" "what is it"
                   "level" "guided"}))]
    (is (re-find #"p-gloss" (:body r)))
    (is (re-find #"is a bird" (:body r)) "composed from `genl`'s own comment")
    (testing "and the formal sentence is still on the row above it"
      (is (re-find #"class=\"sx" (:body r))))))
