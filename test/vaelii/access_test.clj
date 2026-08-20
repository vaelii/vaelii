;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.access-test
  "The read-access facade (`vaelii.impl.access`) and the browser's attach-to-daemon
  mode.  Access dispatches a KB read to an in-process KB or a remote daemon behind one
  surface; the browser is written against that surface, so it renders a KB it owns and
  a KB a daemon owns *the same way*.

  The end-to-end proof is byte equality: the same page rendered over the in-process KB
  and over the daemon (across the wire) must be identical HTML.  That only holds if the
  wire preserves sentence structure — a sentence is a list, and it must not arrive as a
  vector — so this doubles as the regression for `serve/wire-safe`.

  The claim is about **what the KB says**, which is the whole of every page but one
  element: the term page's proposal panel is about what this *process* can do, and
  running a proposal a round-trip at a time against a daemon is not something to offer a
  reader (`access/local-kb` answers nil there).  So the panel is compared for its
  difference and the KB-derived remainder for its equality — weakening neither."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.access :as access]
            [vaelii.impl.serve :as serve]
            [vaelii.impl.web :as web]
            [vaelii.test-util :as tu]))

(def ^:dynamic *remote* nil)

(use-fixtures :once
  (fn [f]
    (let [kb (tu/fresh)]
      ;; the world context is wired below the vocabulary one, as the starter wires
      ;; every real context: the matching fan-out and the disjointness check are
      ;; context-scoped, so an unwired reader would see the facts but not the edges
      (v/assert kb '(genlCx CxNaturalWorld CxCore) 'CxCore)
      (v/assert kb '(genl animal thing) 'CxCore)
      (v/assert kb '(genl dog animal) 'CxCore)
      (v/assert kb '(genl cat animal) 'CxCore)
      (v/assert kb '(disjoint dog cat) 'CxCore)
      (v/assert kb '(dog Muffet) 'CxNaturalWorld)
      (let [server (serve/start kb {:port 0})]
        (try
          (binding [tu/*kb* kb, *remote* (access/remote "localhost" (serve/port server))]
            (f))
          (finally (.stop server) (tu/clear-kb! kb)))))))

;; ---- the two lists that have to agree ------------------------------------

(deftest every-declared-read-op-has-somewhere-to-dispatch-to
  ;; `defreads` names ops; `serve/ops` implements them.  A name in the first with no
  ;; entry in the second compiles, publishes a wrapper, and throws NPE on the nil it
  ;; looks up — at call time, on whichever page or client reaches it first.  Nothing else
  ;; ties the lists together, so this is what does.
  (let [missing (remove serve/ops access/read-ops)]
    (is (empty? missing)
        (str "access declares read ops that serve/ops does not implement: "
             (pr-str (vec missing)))))
  (testing "and the reverse direction is deliberately loose"
    ;; `serve/ops` also carries the writes and anything the browser reaches directly, so
    ;; an op with no access wrapper is a choice rather than a bug — asserted here only so
    ;; that the one-directional check above reads as intended.
    (is (seq (remove (set access/read-ops) (keys serve/ops))))))

;; ---- dispatch: local, raw-kb, and remote agree ---------------------------

(deftest a-raw-kb-and-local-access-answer-like-vaelii-core
  (let [via-core   (map :sentence (v/sentexes-matching tu/*kb* '(dog ?x) 'CxNaturalWorld))
        via-raw    (map :sentence (access/sentexes-matching tu/*kb* '(dog ?x) 'CxNaturalWorld))
        via-local  (map :sentence (access/sentexes-matching (access/local tu/*kb*) '(dog ?x) 'CxNaturalWorld))]
    (is (= '[(dog Muffet)] (vec via-core)))
    (is (= (vec via-core) (vec via-raw) (vec via-local))
        "a raw KB and an explicit local access both take the in-process path")))

(deftest remote-access-answers-across-the-wire-like-local
  (testing "a fact query"
    (is (= (map :sentence (v/sentexes-matching tu/*kb* '(dog ?x) 'CxNaturalWorld))
           (map :sentence (access/sentexes-matching *remote* '(dog ?x) 'CxNaturalWorld)))))
  (testing "specificity — (dog Muffet) answers (animal ?x) — over the wire"
    (is (some #(= 'Muffet (get % '?x)) (access/ask *remote* '(animal ?x) 'CxNaturalWorld))))
  (testing "a taxonomy read (a set of symbols) round-trips"
    (is (= (v/genls tu/*kb* 'dog) (set (access/genls *remote* 'dog)))))
  (testing "a sentence comes back a list, not a vector (wire-safe fidelity)"
    (is (seq? (:sentence (access/sentex *remote*
                                        (access/handle-of *remote* '(dog Muffet) 'CxNaturalWorld)))))))

(deftest contextual-belief-introspection-has-local-remote-parity
  (let [h (v/handle-of tu/*kb* '(dog Muffet) 'CxNaturalWorld)
        expected (v/belief-status tu/*kb* h 'CxNaturalWorld)]
    (is (= (v/believed? tu/*kb* h 'CxNaturalWorld)
           (access/believed? tu/*kb* h 'CxNaturalWorld)
           (access/believed? (access/local tu/*kb*) h 'CxNaturalWorld)
           (access/believed? *remote* h 'CxNaturalWorld)))
    (is (= expected
           (access/belief-status tu/*kb* h 'CxNaturalWorld)
           (access/belief-status (access/local tu/*kb*) h 'CxNaturalWorld)
           (access/belief-status *remote* h 'CxNaturalWorld)))))

(deftest the-vocabulary-reads-the-same-over-the-wire
  ;; a remote client has no records to scan, so term enumeration has to be an op of its
  ;; own — and its ORDER has to survive EDN, which is why `terms` answers a vector
  (testing "enumeration and count"
    (is (= (v/terms tu/*kb*) (vec (access/terms *remote*))))
    (is (= (v/term-count tu/*kb*) (access/term-count *remote*)))
    (is (= (count (v/terms tu/*kb*)) (access/term-count *remote*))))
  (testing "search, with the opts map on the wire"
    (is (= (v/find-terms tu/*kb* "d") (vec (access/find-terms *remote* "d"))))
    (is (= '[dog] (vec (access/find-terms *remote* "dog"))))
    (is (= (v/find-terms tu/*kb* "og" {:match :substring})
           (vec (access/find-terms *remote* "og" {:match :substring}))))
    (is (= '[Muffet] (vec (access/find-terms *remote* "^Muffet$" {:match :regex}))))
    (is (= 2 (count (access/find-terms *remote* "" {:limit 2}))))))

;; ---- the one write: edit, over the wire ----------------------------------

(deftest editing-writes-through-the-daemon
  (testing "edit adds and removes over the wire (the browser's Save path), net-neutral"
    (let [added (:added (access/edit! *remote* {:add [['(bird Sky) 'CxNaturalWorld]]
                                                :remove []}))
          h     (first added)]
      (is (some? h) "the remote assert returns a handle")
      (is (seq (access/sentexes-matching *remote* '(bird Sky) 'CxNaturalWorld))
          "the asserted fact is visible over the wire")
      (access/edit! *remote* {:add [] :remove [h]})
      (is (empty? (access/sentexes-matching *remote* '(bird Sky) 'CxNaturalWorld))
          "and removing it over the wire takes it back out"))))

;; ---- the browser renders a daemon-owned KB identically -------------------

(defn- GET [app uri qs]
  (app (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- kb-part
  "A term page up to the proposal panel — everything the KB is the author of.  The panel
  is what the *process* can do rather than what the KB holds, and it is the last element
  on the page, so cutting at it leaves exactly the part both targets must agree on."
  [body]
  (subs body 0 (or (str/index-of body "<div class=\"propose\"") (count body))))

(deftest browser-over-a-daemon-matches-the-in-process-render
  (let [local-app  (web/app tu/*kb*)
        remote-app (web/app *remote*)]
    (testing "the term page reflects the daemon's KB and matches local byte for byte"
      (let [lr (GET local-app "/term" "q=dog")
            rr (GET remote-app "/term" "q=dog")]
        (is (= 200 (:status rr)))
        (is (re-find #"Muffet" (:body rr)) "the daemon's fact renders")
        (is (re-find #"Disjoint" (:body rr)) "dog ⊥ cat renders from the daemon")
        (is (= (kb-part (:body lr)) (kb-part (:body rr)))
            "remote browsing is identical to in-process browsing")))
    (testing "the one exception, and it says why rather than offering a dead button"
      (let [lr (GET local-app "/term" "q=dog")
            rr (GET remote-app "/term" "q=dog")]
        (is (re-find #"hx-post=\"/propose\"" (:body lr)))
        (is (not (re-find #"hx-post=\"/propose\"" (:body rr))))
        (is (re-find #"attached to a daemon" (:body rr)))))
    (testing "the default page too"
      (is (= (:body (GET local-app "/" nil))
             (:body (GET remote-app "/" nil)))))
    (testing "a sentex page (handle-addressed) matches"
      (let [h (v/handle-of tu/*kb* '(dog Muffet) 'CxNaturalWorld)]
        (is (= (:body (GET local-app (str "/sentex/" h) nil))
               (:body (GET remote-app (str "/sentex/" h) nil))))))))
