;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.serve-test
  "The operational surface: the EDN-over-HTTP daemon (`vaelii.impl.serve`) and its
  client (`vaelii.impl.client`).

  Two levels.  The handler is pure `request -> response`, so `app` is exercised
  without a socket — the fast, deterministic check that ops dispatch, results are
  EDN-clean, and bad input is refused.  Then one full loop starts jetty on an
  ephemeral port and drives it with the real client, proving the wire round-trips
  end to end: sentences out as symbol s-expressions, sentex records back as plain
  maps.

  Every test says which **posture** its daemon is in rather than letting the
  environment decide: `open-app` serves with no token (the loopback default, and the
  only handler under which the other refusals are reachable at all), `token` and
  `authed-app` serve with one.  A `VAELII_API_TOKEN` in the shell running the suite
  therefore changes nothing here."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.client :as client]
            [vaelii.impl.config :as config]
            [vaelii.impl.guard :as guard]
            [vaelii.impl.llm.tools :as tools]
            [vaelii.impl.serve :as serve]
            [vaelii.impl.subscribe :as sub]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [org.eclipse.jetty.server Server ServerConnector]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private token
  "The one token the authenticated tests below share.  A fixture rather than a per-test
  string, so what a test varies is the *header*, which is the thing under test."
  "s3cret-token")

(defn- open-app
  "`serve/app` with **no** token — the loopback default, and the handler every test of
  another refusal needs: one that 401s first exercises none of them.  Explicit rather
  than defaulted, since the default reads `VAELII_API_TOKEN` and the suite must not
  answer differently in a shell that has one."
  [kb]
  (serve/app kb {:token nil}))

(defn- authed-app
  "`serve/app` holding `token` — the posture a public bind is required to be in."
  [kb]
  (serve/app kb {:token token}))

(defn- post-op*
  "Call `handler` (from `serve/app`) with a POST /op carrying `{:op :args}` under
  exactly `headers`, and return the parsed EDN reply — no socket.  What `post-op`
  always sends, this lets a test withhold or misspell, which is how the guards'
  refusal paths are driven."
  [handler headers op args]
  (let [body (pr-str {:op op :args (vec args)})
        resp (handler {:request-method :post :uri "/op"
                       :headers headers
                       :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})]
    (assoc (edn/read-string (:body resp)) :status (:status resp))))

(defn- post-op
  "`post-op*` with the headers a real client sends.

  The `content-type` is not decoration: `guard/edn-body?` refuses the write route
  without it, which is the CSRF guard rather than a parsing one (a cross-site `fetch`
  cannot set this type without a preflight the daemon will not answer).  A real client
  sends it, so the helper that stands in for one has to as well.  `Origin`/`Referer` are
  deliberately absent — `guard/same-origin?` treats a request carrying neither as
  same-origin, which is what a non-browser client is."
  [handler op args]
  (post-op* handler {"content-type" "application/edn"} op args))

(defn- post-form
  "POST `form` exactly as given — no `{:op :args}` shaping — which is how a
  malformed request body itself is driven."
  [handler form]
  (let [body (pr-str form)
        resp (handler {:request-method :post :uri "/op"
                       :headers {"content-type" "application/edn"}
                       :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})]
    (assoc (edn/read-string (:body resp)) :status (:status resp))))

;; ---- the handler, no socket ---------------------------------------------

(tu/deftest-kb app-dispatches-ops-and-refuses-bad-input
  (tu/with-terms [dog animal Muffet CxServe]
    (let [handler (open-app kb)]
      (testing "an assert op stores and returns the handle"
        (let [r (post-op handler :assert [(list dog Muffet) CxServe {:strength :monotonic}])]
          (is (:ok r))
          (is (nat-int? (:result r)))))
      (testing "a query op returns sentex maps — plain, not records"
        (let [r (post-op handler :sentexes-matching [(list dog '?x) CxServe])]
          (is (:ok r))
          (let [sx (first (:result r))]
            (is (map? sx))
            (is (not (record? sx)) "a record must be projected to a plain map on the wire")
            (is (= (list dog Muffet) (:sentence sx))))))
      (testing "an ask op returns binding maps"
        (v/assert kb (list 'genl dog animal) CxServe)
        (let [r (post-op handler :ask [(list animal '?x) CxServe])]
          (is (:ok r))
          (is (some #(= Muffet (get % '?x)) (:result r))
              "specificity: (dog Muffet) answers the (animal ?x) goal")))
      (testing "why returns a proof-tree map"
        (let [h (v/handle-of kb (list dog Muffet) CxServe)
              r (post-op handler :why [h])]
          (is (:ok r))
          (is (map? (:result r)))
          (is (= (list dog Muffet) (:sentence (:result r))))))
      (testing "contextual belief and its status dispatch as EDN-clean reads"
        (let [h (v/handle-of kb (list dog Muffet) CxServe)
              believed-r (post-op handler :believed? [h CxServe])
              status-r   (post-op handler :belief-status [h CxServe])]
          (is (= {:ok true :result true :status 200} believed-r))
          (is (:ok status-r))
          (is (= h (get-in status-r [:result :handle])))
          (is (true? (get-in status-r [:result :visible?])))))
      (testing "preview answers what a batch would believe, and stores nothing"
        ;; served with the writes because it applies the batch and rolls it back — the
        ;; daemon is the single writer, which is exactly the condition it needs
        (tu/with-terms [swims Willy]
          (let [before (tu/sentex-ids kb)
                r (post-op handler :preview
                           [{:add [[(list swims Willy) CxServe]]}])]
            (is (:ok r))
            (is (= [(list swims Willy)]
                   (mapv :sentence (:believed-added (:result r))))
                "the answer crosses the wire as sentences, not records")
            (is (= before (tu/sentex-ids kb))
                "a preview over the wire stored something")
            (is (nil? (v/handle-of kb (list swims Willy) CxServe))))))
      (testing "an unknown op is a 400 that lists the real ops"
        (let [r (post-op handler :not-an-op [])]
          (is (false? (:ok r)))
          (is (= 400 (:status r)))
          (is (some #{:assert} (:ops r)))))
      (testing "a refusal (a non-ground fact) comes back as an error, not a crash"
        (let [r (post-op handler :assert [(list dog '?x) CxServe])]
          (is (false? (:ok r)))
          (is (= :not-ground (:type r)) "the ex-data :type rides the wire")))
      (testing "a non-sequential :args is the caller's mistake — 400 :bad-args with a
                usable :type, not a bare 500 with none"
        (let [r (post-form handler {:op :assert :args 5})]
          (is (= 400 (:status r)))
          (is (false? (:ok r)))
          (is (= :bad-args (:type r))))))))

(tu/deftest-kb a-fault-the-daemon-cannot-name-still-answers-with-a-type
  ;; The floor under the one-vocabulary promise `docs/operations.md` makes.  An entry point that
  ;; fails for a reason nothing here classifies — a record store that will not answer, a
  ;; solver binary that is not on the host — must still hand a caller a keyword to catch
  ;; on: `:type nil` is the key present and useless, which is the one answer worse than
  ;; either.  Both arms, because a throw reaches the handler two ways and only one of
  ;; them carries `ex-data` at all.
  (let [handler (open-app kb)
        answer  (fn [thrown]
                  ;; the fault is logged at :warn on the way past, which is the daemon
                  ;; doing its job rather than something for a test run to print
                  (binding [trove/*log-fn* (fn [& _] nil)]
                    (with-redefs [serve/ops (assoc serve/ops :sentex-count
                                                   (fn [_kb _args] (throw thrown)))]
                      (post-op handler :sentex-count []))))]
    (testing "an ex-info whose ex-data names no type"
      (let [r (answer (ex-info "the record store would not answer" {:handle 7}))]
        (is (= 500 (:status r)))
        (is (false? (:ok r)))
        (is (= :internal-error (:type r)))))
    (testing "and a bare Java exception, which carries no ex-data at all"
      (let [r (answer (RuntimeException. "the record store would not answer"))]
        (is (= 500 (:status r)))
        (is (false? (:ok r)))
        (is (= :internal-error (:type r)))))
    (testing "a fault that does name itself keeps its own :type, so the default is a
              floor rather than a flattening"
      (let [r (answer (ex-info "belief was never rebuilt" {:type :unrecovered-kb}))]
        (is (= 500 (:status r)))
        (is (= :unrecovered-kb (:type r)))))
    (testing "and the op answers normally with nothing redefined, so the three above are
              the throw's doing and not the handler's"
      (let [r (post-op handler :sentex-count [])]
        (is (:ok r))
        (is (nat-int? (:result r)))))))

;; ---- the guards' refusal paths -------------------------------------------

(tu/deftest-kb post-op-refuses-a-cors-simple-content-type
  ;; the CSRF gate: `application/edn` is not a CORS-*simple* type, so a browser must
  ;; preflight it and this daemon answers no preflight — demanding it is what keeps a
  ;; page the operator merely visits from driving the write route
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)
          refused (fn [headers]
                    (post-op* handler headers :assert [(list dog Muffet) CxServe]))]
      (testing "no content-type at all is a 415 in the daemon's structured error shape"
        (let [r (refused {})]
          (is (= 415 (:status r)))
          (is (false? (:ok r)))
          (is (= :not-edn (:type r)) "the ex-data :type rides the wire")
          (is (string? (:error r)))))
      (testing "the three types a cross-site fetch may send without a preflight are refused"
        (doseq [ct ["text/plain"
                    "application/x-www-form-urlencoded"
                    "multipart/form-data"]]
          (let [r (refused {"content-type" ct})]
            (is (= 415 (:status r)) ct)
            (is (= :not-edn (:type r)) ct))))
      (testing "and the refusal runs nothing — the op is never executed"
        (is (= before (tu/sentex-ids kb)))
        (is (nil? (v/handle-of kb (list dog Muffet) CxServe)))))))

(tu/deftest-kb post-op-refuses-a-cross-origin-caller
  ;; the other CSRF gate, and the one that bites when a browser *does* stamp an origin:
  ;; `edn-body?` forces a preflight this daemon will not answer, and this refuses the
  ;; page that got one anyway.  A `:type` on the wire because a client discriminating on
  ;; the message string is discriminating on prose.
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)
          from    (fn [hdrs]
                    (post-op* handler (merge {"content-type" "application/edn"} hdrs)
                              :assert [(list dog Muffet) CxServe]))]
      (doseq [[label hdrs] [["another site" {"host" "localhost:4200"
                                             "origin" "http://evil.example"}]
                            ;; a sandboxed frame sends `Origin: null` — an origin claim
                            ;; matching nothing, not an absent header
                            ["an opaque origin" {"host" "localhost:4200" "origin" "null"}]
                            ["a cross-site referer" {"host" "localhost:4200"
                                                     "referer" "http://evil.example/x"}]]]
        (let [r (from hdrs)]
          (is (= 403 (:status r)) label)
          (is (false? (:ok r)) label)
          (is (= :cross-origin (:type r)) label)))
      (testing "the daemon's own page still writes, so the refusal is the origin's doing"
        (let [r (from {"host" "localhost:4200" "origin" "http://localhost:4200"})]
          (is (= 200 (:status r)))
          (is (:ok r))))
      (testing "and the three refusals ran nothing — only the same-origin write landed"
        (is (= 1 (count (set/difference (tu/sentex-ids kb) before))))))))

(tu/deftest-kb post-op-accepts-edn-however-legally-spelled
  ;; `guard/edn-body?` trims, lower-cases and prefix-matches, so a parameterized or
  ;; case-varied header is still the declaration the gate requires
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)]
      (doseq [ct ["application/edn; charset=utf-8"
                  "Application/EDN"
                  "APPLICATION/EDN; CHARSET=UTF-8"
                  "  application/edn  "]]
        (let [r (post-op* handler {"content-type" ct} :assert
                          [(list dog Muffet) CxServe])]
          (is (= 200 (:status r)) ct)
          (is (:ok r) ct)))
      (is (some? (v/handle-of kb (list dog Muffet) CxServe))
          "the accepted spelling reached the op — the fact is stored"))))

(tu/deftest-kb the-daemon-refuses-a-rebound-host-on-every-route
  ;; the DNS-rebinding gate: `same-origin?` folds when the attacker controls both
  ;; `Origin` and `Host` (a domain re-resolving to 127.0.0.1), so `host-allowed?` is
  ;; the check that has to hold — and it wraps the whole server, because a rebound
  ;; page reads the KB as happily as it writes to it
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)]
      (testing "a write op under a rebound Host is a 400 before anything runs"
        (let [r (post-op* handler {"content-type" "application/edn"
                                   "host"   "evil.example.com"
                                   "origin" "http://evil.example.com"}
                          :assert [(list dog Muffet) CxServe])]
          (is (= 400 (:status r)))
          (is (false? (:ok r)))
          (is (= :bad-host (:type r)))
          (is (= before (tu/sentex-ids kb)) "the refused op stored nothing")
          (is (nil? (v/handle-of kb (list dog Muffet) CxServe)))))
      (testing "a read route is refused too — the KB is what a rebound page came for"
        (let [r (handler {:request-method :get :uri "/health"
                          :headers {"host" "evil.example.com:4200"}})]
          (is (= 400 (:status r)))
          (is (= :bad-host (:type (edn/read-string (:body r)))))))
      (testing "the daemon's own names still pass, with or without a port"
        (doseq [h ["localhost:4200" "127.0.0.1:4200" "[::1]:4200" "localhost"]]
          (let [r (handler {:request-method :get :uri "/health" :headers {"host" h}})]
            (is (= 200 (:status r)) h))))
      (testing "a write under the daemon's own Host still lands"
        (let [r (post-op* handler {"content-type" "application/edn"
                                   "host" "127.0.0.1:4200"}
                          :assert [(list dog Muffet) CxServe])]
          (is (:ok r))
          (is (nat-int? (:result r)))))
      (testing "and a Host-less request (curl, every other test here) passes by design"
        (is (= 200 (:status (handler {:request-method :get :uri "/health"}))))))))

(tu/deftest-kb export-over-the-wire-writes-on-the-daemons-own-host
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)
          root (.toFile (Files/createTempDirectory "vaelii-serve-export-"
                                                   (into-array FileAttribute [])))
          dump (java.io.File. root "a-dump")]
      (try
        (v/assert kb (list dog Muffet) CxServe)
        (testing "the op answers with the writer's summary — every value already EDN, so
                  nothing about it needs the sentex-map projection"
          (let [r (post-op handler :export [(.getPath dump) {:compression :none}])]
            (is (:ok r))
            (is (= (v/sentex-count kb) (:sentexes (:result r))))
            (is (= (.getAbsolutePath dump) (:dir (:result r))))))
        (testing "and the directory it names is one on this host — the daemon's — which is
                  the only place it could be: there is no stream to hand a client back"
          (is (= :dump (catalog/classify dump))))
        (testing "a refusal crosses the wire as the writer's own message"
          (let [r (post-op handler :export [(.getPath dump) {}])]
            (is (false? (:ok r)))
            (is (re-find #"is not empty" (:error r)))
            (is (= :not-empty (:type r)))))
        (finally (doseq [^File f (reverse (file-seq root))] (.delete f)))))))

;; ---- the shared bearer token ---------------------------------------------

(defn- post-with-auth
  "POST a `:contexts` op under `auth` as the `Authorization` header (nil sends none),
  and answer the raw response — the *headers* are half of what a 401 promises, so this
  one does not parse the reply away."
  [handler auth]
  (let [body (pr-str {:op :contexts :args []})]
    (handler {:request-method :post :uri "/op"
              :headers (cond-> {"content-type" "application/edn"}
                         auth (assoc "authorization" auth))
              :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})))

(tu/deftest-kb no-way-of-not-holding-the-token-is-told-from-another
  ;; The refusal is the test, and the four ways of failing it have to be
  ;; indistinguishable: a 401 that said *which* — "malformed header" against "wrong
  ;; token", or a different message for a right prefix — is an oracle a caller walks a
  ;; byte at a time.  Same status, same body, same challenge, whatever went wrong.
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (authed-app kb)
          before  (tu/sentex-ids kb)
          bodies  (atom #{})]
      (doseq [[label auth] [["no Authorization header at all"      nil]
                            ["a wrong token"                       "Bearer wrong"]
                            ["a token with the right prefix"       (str "Bearer " (subs token 0 4))]
                            ["the right token with more after it"  (str "Bearer " token "x")]
                            ["a malformed Authorization line"      token]
                            ["another scheme entirely"             "Basic czNjcmV0"]
                            ["the scheme with no token after it"   "Bearer "]]]
        (let [resp (post-with-auth handler auth)
              r    (edn/read-string (:body resp))]
          (is (= 401 (:status resp)) label)
          (is (false? (:ok r)) label)
          (is (= :unauthorized (:type r)) label)
          (is (= "Bearer" (get-in resp [:headers "www-authenticate"]))
              (str label " — a 401 carries the challenge the status code is defined to"))
          (is (= "application/edn" (get-in resp [:headers "content-type"]))
              (str label " — the refusal is EDN like every other one"))
          (swap! bodies conj (:body resp))))
      (testing "and every one of them is the same body, byte for byte"
        (is (= 1 (count @bodies))))
      (testing "the token itself is accepted, so the refusals are the header's doing"
        (is (= 200 (:status (post-with-auth handler (str "Bearer " token))))))
      (testing "and the scheme is matched case-insensitively, as RFC 7235 defines it"
        (is (= 200 (:status (post-with-auth handler (str "bearer " token))))))
      (testing "nothing the refusals asked for ran"
        (is (= before (tu/sentex-ids kb)))))))

(tu/deftest-kb health-answers-unauthenticated-and-nothing-else-does
  ;; The one carve-out, and the reason for it: a daemon only its token-holder can probe
  ;; is one no orchestrator, load balancer or shell script can watch, and `{:ok true}`
  ;; reveals nothing a caller did not learn by connecting.  The other side is driven off
  ;; `serve/op-names` itself, so an op added to either table later is covered by
  ;; construction.
  (let [handler (authed-app kb)]
    (testing "GET /health answers with no credential"
      (let [resp (handler {:request-method :get :uri "/health"})]
        (is (= 200 (:status resp)))
        (is (:ok (edn/read-string (:body resp))))))
    (testing "and every op the daemon answers is refused without one — both tables, so
              a feed subscription is no more allocatable by an anonymous caller than a
              read is answerable to one"
      (doseq [op serve/op-names]
        (let [body (pr-str {:op op :args []})
              resp (handler {:request-method :post :uri "/op"
                             :headers {"content-type" "application/edn"}
                             :body (ByteArrayInputStream.
                                    (.getBytes ^String body "UTF-8"))})]
          (is (= 401 (:status resp)) (str op))
          (is (= :unauthorized (:type (edn/read-string (:body resp)))) (str op)))))
    (testing "a route nothing serves is refused before the 404, since the router's
              answer is not a thing an anonymous caller is owed either"
      (is (= 401 (:status (handler {:request-method :get :uri "/nothing-here"})))))))

(clojure.test/deftest the-token-comparison-is-one-named-constant-time-fn
  ;; Asserted structurally rather than by timing: a wall-clock assertion over a
  ;; nanosecond difference is flaky by construction on a machine running anything else,
  ;; and would fail on a laptop that throttled mid-run.  What is pinnable is that the
  ;; comparison is one fn (`MessageDigest/isEqual` over UTF-8 bytes, which reads every
  ;; byte whatever the lengths) and that it answers correctly either side of equal
  ;; length — the two cases a `=` on strings would short-circuit differently.  It lives
  ;; in `guard` because both servers compare a token through it.
  (let [matches? guard/bearer-matches?]
    (testing "equal length"
      (is (true?  (matches? "s3cret-token" "s3cret-token")))
      (is (false? (matches? "s3cret-token" "s3cret-tokeN")))
      (is (false? (matches? "s3cret-token" "X3cret-token"))))
    (testing "unequal length, either way"
      (is (false? (matches? "s3cret-token" "s3cret-toke")))
      (is (false? (matches? "s3cret-token" "s3cret-tokens")))
      (is (false? (matches? "s3cret-token" ""))))
    (testing "the bytes are UTF-8, so a non-ASCII token compares as itself"
      (is (true?  (matches? "sécret-ключ" "sécret-ключ")))
      (is (false? (matches? "sécret-ключ" "secret-ключ"))))))

(clojure.test/deftest a-bind-that-names-an-address-without-a-token-is-refused
  ;; Fail closed, both arms.  `--listen` is the flag that publishes `POST /op` — the
  ;; KB's only writer — *and* the flag that drops the `Host` allowlist, so without this
  ;; the exposed configuration is the one with the fewest checks.  The loopback default
  ;; is deliberately not held to it: `lein serve` on a laptop is a real workflow, and a
  ;; credential required there only teaches an operator to export a constant.
  (let [posture #'serve/auth-posture]
    (testing "loopback with no token starts, open — however the interface is spelled"
      (doseq [h ["127.0.0.1" "localhost" "[::1]" "::1" "0:0:0:0:0:0:0:1"]]
        (is (= :open (posture h nil)) h))
      (is (= :open (posture "127.0.0.1" "")) "a blank token is an unset one")
      (is (= :open (posture "127.0.0.1" "   "))))
    (testing "a token puts either bind in the authenticated posture"
      (is (= :required (posture "127.0.0.1" "s3cret")))
      (is (= :required (posture "0.0.0.0" "s3cret"))))
    (testing "and an address with no token is refused, typed"
      (doseq [h ["0.0.0.0" "10.0.0.4" "::" "example.internal"]]
        (let [e (is (thrown? clojure.lang.ExceptionInfo (posture h nil)) h)]
          (is (= :unauthorized (:type (ex-data e))) h)
          (is (= h (:host (ex-data e))) h)
          (is (re-find #"VAELII_API_TOKEN" (ex-message e)) h))))))

(clojure.test/deftest the-daemon-says-which-posture-it-started-in
  ;; A test of the log *line*, not of the absence of one: an operator reading a machine
  ;; after an incident needs to find which posture it was in, and silence on the open
  ;; one is indistinguishable from a daemon that never started.
  (let [logged (atom [])
        run!   (fn [host posture hosts]
                 (reset! logged [])
                 (binding [trove/*log-fn*
                           (fn [_ns _coords level id _payload]
                             (swap! logged conj [level id]) nil)]
                   (#'serve/announce-auth! host posture hosts))
                 @logged)]
    (testing "loopback with no token starts, and warns naming the flag"
      (is (= [[:warn ::serve/no-token]] (run! "127.0.0.1" :open :allowlisted))))
    (testing "a token is said out loud too — both postures are on the record"
      (is (= [[:info ::serve/authenticated]] (run! "127.0.0.1" :required :allowlisted))))
    (testing "a public bind adds the line about what a token still does not cover"
      (is (= [[:info ::serve/authenticated] [:warn ::serve/public-bind]]
             (run! "0.0.0.0" :required :allowlisted))))
    (testing "an open Host allowlist on a public bind warns too, named apart from the
              token so a reader distinguishes which check is missing"
      (is (= [[:info ::serve/authenticated] [:warn ::serve/public-bind]
              [:warn ::serve/open-hosts]]
             (run! "0.0.0.0" :required :open))))))

(clojure.test/deftest host-posture-follows-the-allowlist
  (let [posture #'serve/host-posture]
    (testing "loopback is always allowlisted, token or not"
      (is (= :allowlisted (posture "127.0.0.1"))))
    (testing "a public bind is open unless VAELII_ALLOWED_HOSTS names something"
      (if (some? (System/getenv "VAELII_ALLOWED_HOSTS"))
        (println "SKIP vaelii.serve-test/host-posture-follows-the-allowlist:"
                 "VAELII_ALLOWED_HOSTS is set in this environment")
        (is (= :open (posture "0.0.0.0")))))))

;; ---- the search ceiling --------------------------------------------------
;;
;; The other thing a caller spends: not the daemon's heap but its **writer**.  Every op
;; runs under the one monitor, so a read a caller sized holds every other request behind
;; it — and the two dials a caller sizes it with are `:max-depth` and `:max-ms`.  The
;; ceiling is applied in `serve/ops` rather than at this route, because the model's tool
;; surface dispatches through the same table; the test below reads both entry points.

(tu/deftest-kb a-bound-over-the-ceiling-is-refused-and-one-under-it-is-not
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)]
      (post-op handler :assert [(list dog Muffet) CxServe])
      (testing "a depth inside the ceiling answers"
        (let [r (post-op handler :query [(list dog '?x) CxServe {:max-depth 3}])]
          (is (true? (:ok r)))
          (is (= [{'?x Muffet}] (:result r)))))
      (testing "the ceiling itself is admitted — the bound is what a request may name"
        (is (true? (:ok (post-op handler :query
                                 [(list dog '?x) CxServe
                                  {:max-depth (config/max-query-depth)}])))))
      (testing "and one past it is refused by name, with the figure both sides"
        (let [r (post-op handler :query [(list dog '?x) CxServe
                                         {:max-depth (inc (config/max-query-depth))}])]
          (is (false? (:ok r)))
          (is (= :over-ceiling (:type r)) "the ex-data :type rides the wire")
          (is (= 400 (:status r)) "a caller's request, so a client error")
          (is (re-find #"ceiling" (:error r)))))
      (testing "a wall clock past the ceiling is refused the same way"
        (let [r (post-op handler :ask-within [(list dog '?x) CxServe
                                              {:max-ms (inc (config/max-query-ms))}])]
          (is (false? (:ok r)))
          (is (= :over-ceiling (:type r)))))
      (testing "and an anytime read that names no clock is given the ceiling's, since
                absent there means no clock at all"
        (let [r (post-op handler :ask-within [(list dog '?x) CxServe {}])]
          (is (true? (:ok r)))
          (is (= :complete (:status (:result r))) "a small KB finishes well inside it")))
      (testing "an op with no bound of its own is untouched — there is nothing to raise"
        (is (true? (:ok (post-op handler :handle-of [(list dog Muffet) CxServe]))))
        (is (true? (:ok (post-op handler :sentexes-matching
                                 [(list dog '?x) CxServe]))))))))

(tu/deftest-kb the-four-backward-search-entry-points-are-held-to-the-ceiling-too
  ;; `:ask`, `:ask?`, `:prove` and `:provable?` each take a bound now, and each runs on
  ;; the daemon's single write monitor — so a caller sizing one sizes every other
  ;; caller's wait.  What is different from `:query` is that a request may name no option
  ;; map at all, and absent `:max-ms` is *no clock*: the daemon fills its own in rather
  ;; than serving an unbounded backward search.
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)]
      (post-op handler :assert [(list dog Muffet) CxServe])
      (testing "a clock past the ceiling is refused by name"
        (let [r (post-op handler :ask [(list dog '?x) CxServe
                                       {:max-ms (inc (config/max-query-ms))}])]
          (is (false? (:ok r)))
          (is (= :over-ceiling (:type r)))
          (is (= 400 (:status r)) "a caller's request, so a client error")))
      (testing "and a depth past it, at the two entry points that expand rules"
        (let [r (post-op handler :prove [(list dog '?x) CxServe
                                         {:max-depth (inc (config/max-query-depth))}])]
          (is (false? (:ok r)))
          (is (= :over-ceiling (:type r))))
        (let [r (post-op handler :provable? [(list dog '?x) CxServe
                                             {:max-depth (inc (config/max-query-depth))}])]
          (is (false? (:ok r)))
          (is (= :over-ceiling (:type r)))))
      (testing "a request that names no option map is padded out to the arity that has
                one, so the ceiling's clock reaches a short call too"
        (is (true? (:ok (post-op handler :ask [(list dog '?x) CxServe]))))
        (is (true? (:ok (post-op handler :ask? [(list dog '?x) CxServe]))))
        (is (true? (:ok (post-op handler :provable? [(list dog '?x) CxServe]))))
        (is (= [Muffet] (mapv #(get % '?x) (:result (post-op handler :prove
                                                             [(list dog '?x)]))))
            "including one that named no context either — the arguments in between are
             filled with the entry point's own defaults, so the read is the ?ctx fan it would
             have been in process"))
      (testing "and a search that reaches its clock is a 400 rather than a run that
                holds the writer while nobody waits for the answer"
        (let [r (post-op handler :prove [(list dog '?x) CxServe {:max-ms 0}])]
          (is (false? (:ok r)))
          (is (= :budget-exhausted (:type r)))
          (is (= 400 (:status r))))))))

(tu/deftest-kb integrity-requests-are-clamped-and-release-the-monitor-on-exhaustion
  (tu/with-terms [widget slowEnough required wrote CxServe]
    (let [entered (atom nil)]
      (v/add-evaluatable kb slowEnough
                         (fn [_]
                           (when-let [signal @entered] (deliver signal true))
                           (Thread/sleep 5)
                           true))
      (v/add-evaluatable kb required (constantly false))
      (v/assert kb (list 'defnSufficient widget (list slowEnough '?x)) CxServe)
      (v/assert kb (list 'defnNecessary widget (list required '?x)) CxServe)
      (let [handler (open-app kb)]
        (testing "explicit nil options are the same request at every local/daemon arity"
          (let [local    (v/kb-integrity kb #{7} CxServe nil)
                omitted (:result (post-op handler :kb-integrity [#{7} CxServe]))
                explicit (:result (post-op handler :kb-integrity [#{7} CxServe nil]))]
            (is (= local omitted explicit))))
        (with-redefs [serve/integrity-max-work 1000
                      serve/integrity-max-results 20]
          (testing "a caller may lower but not raise either daemon-owned ceiling"
            (doseq [[option value] [[:max-work 1001] [:max-results 21]]]
              (let [r (post-op handler :kb-integrity
                               [#{7} CxServe {option value :max-ms 1000}])]
                (is (false? (:ok r)))
                (is (= :over-ceiling (:type r)))
                (is (re-find (re-pattern (name option)) (:error r))))))
          (testing "an omitted options map receives all three ceilings, and a queued writer proceeds"
            (let [signal (promise)
                  _      (reset! entered signal)
                  audit  (future (post-op handler :kb-integrity
                                          [(set (range 100)) CxServe]))]
              (is (= true (deref signal 2000 ::timeout))
                  "the audit reached KB-owned condition work while holding the monitor")
              (let [writer (future (post-op handler :assert [(list wrote 1) CxServe]))
                    ar     (deref audit 3000 ::timeout)
                    wr     (deref writer 3000 ::timeout)]
                (is (not= ::timeout ar) "the work ceiling ends the oversized audit")
                (is (= :truncated (get-in ar [:result :status])))
                (is (= :max-work (get-in ar [:result :reason])))
                (is (not= :audited (get-in ar [:result :status])))
                (is (not= ::timeout wr) "the queued writer acquires the released monitor")
                (is (:ok wr))
                (is (v/ask? kb (list wrote 1) CxServe))))))))))

(tu/deftest-kb the-models-tool-surface-is-held-to-the-same-ceiling
  ;; `vaelii.impl.llm.tools` generates its schemas from `serve/ops` and calls back into
  ;; it, so a ceiling applied at the HTTP route would be a ceiling the model does not
  ;; have — which is the entry point a prompt-injected model would find first.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (testing "a depth inside the ceiling answers"
      (is (true? (:ok (tools/call kb "kb_query" {"goal" (str (list dog '?x))
                                                 "context" "CxUniverse"
                                                 "opts" "{:max-depth 3}"})))))
    (testing "and one past it comes back as the refusal a tool result carries"
      (let [r (tools/call kb "kb_query" {"goal" (str (list dog '?x))
                                         "context" "CxUniverse"
                                         "opts" (str {:max-depth
                                                      (inc (config/max-query-depth))})})]
        (is (false? (:ok r)))
        (is (re-find #"over-ceiling" (:error r)) "the :type is named for the model too")))
    (testing "and the same at kb_ask, whose ceiling is the clock"
      (let [r (tools/call kb "kb_ask" {"goal" (str (list dog '?x))
                                       "context" "CxUniverse"
                                       "opts" (str {:max-ms (inc (config/max-query-ms))})})]
        (is (false? (:ok r)))
        (is (re-find #"over-ceiling" (:error r)))))))

;; ---- the body ceiling ----------------------------------------------------
;;
;; A caller who can reach `POST /op` is a caller who can spend the daemon's heap by
;; streaming a body at it — and on the open loopback default that is every process on
;; the machine.  The reading half — that the refusal happens *while* reading rather than
;; after — is `vaelii.guard-test`, where the ceiling lives; what belongs here is that the
;; refusal reaches the wire as a 413 in the daemon's own error shape, and that no op ran
;; behind it.

(tu/deftest-kb an-oversized-post-is-a-413-that-runs-no-op
  (tu/with-terms [dog Muffet CxServe]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)
          body    (.getBytes ^String (pr-str {:op :assert
                                              :args [(list dog Muffet) CxServe]})
                             "UTF-8")
          resp    (with-redefs [guard/max-body-bytes 8]
                    (handler {:request-method :post :uri "/op"
                              :headers {"content-type" "application/edn"}
                              :body (ByteArrayInputStream. body)}))
          r       (edn/read-string (:body resp))]
      (is (= 413 (:status resp)))
      (is (false? (:ok r)))
      (is (= :body-too-large (:type r)) "the ex-data :type rides the wire")
      (is (re-find #"exceeds" (:error r)))
      (testing "and the op never ran — the refusal is before the dispatch, not after"
        (is (= before (tu/sentex-ids kb)))
        (is (nil? (v/handle-of kb (list dog Muffet) CxServe))))
      (testing "the same call under the shipped ceiling lands, so the 413 above is the
                ceiling's doing and not the request's"
        (let [r2 (edn/read-string
                  (:body (handler {:request-method :post :uri "/op"
                                   :headers {"content-type" "application/edn"}
                                   :body (ByteArrayInputStream. body)})))]
          (is (:ok r2))
          (is (nat-int? (:result r2))))))))

;; ---- what it binds -------------------------------------------------------

(tu/deftest-kb the-daemon-binds-loopback-unless-told-otherwise
  ;; `POST /op` is the write route of the **single writer**, and a loopback daemon is
  ;; allowed to run with no token, so the default has to answer only this machine — the
  ;; same rule the browser holds to, and the more consequential of the two.  Jetty binds
  ;; every interface when no host is given, so "we passed no host" is precisely the bug:
  ;; this reads the connector rather than the options, because the options are what was
  ;; wrong.
  (let [bound-host (fn [opts]
                     (let [^Server server (serve/start kb opts)]
                       (try
                         (.getHost ^ServerConnector (first (.getConnectors server)))
                         (finally (.stop server)))))]
    (is (= "127.0.0.1" (bound-host {:port 0}))
        "the daemon bound every interface — with no host given, jetty does, and POST /op
         is then a write route reachable off-machine")
    (testing "and an explicit address is still honoured"
      (is (= "127.0.0.1" (bound-host {:port 0 :host "127.0.0.1"}))))))

;; ---- the full wire loop --------------------------------------------------

(tu/deftest-kb client-round-trips-through-the-daemon
  (tu/with-terms [bird flies penguin Tweety CxWire]
    (let [server (serve/start kb {:port 0 :token nil})]
      (try
        (let [conn (client/client "localhost" (serve/port server) {:token nil})]
          (testing "health"
            (is (:ok (client/health conn))))
          (testing "assert / query round-trip over the socket"
            (is (nat-int? (client/assert conn (list bird Tweety) CxWire)))
            (let [rs (client/sentexes-matching conn (list bird '?x) CxWire)]
              (is (= (list bird Tweety) (:sentence (first rs))))))
          (testing "explicit nil integrity options match local and daemon defaults"
            (is (= (v/kb-integrity kb #{} CxWire nil)
                   (client/kb-integrity conn #{} CxWire nil))))
          (testing "a forward rule fires server-side and the derived fact is asked back"
            (client/assert-rule conn [(list bird '?b)] (list flies '?b) CxWire)
            (is (client/ask? conn (list flies Tweety) CxWire)))
          (testing "why over the wire returns a proof tree"
            (let [h (client/handle-of conn (list flies Tweety) CxWire)]
              (is (map? (client/why conn h)))))
          (testing "and a truncated one is re-askable deeper, which is what the opts
                    arity is for: the bound clips a branch to `{:truncated? true}`, and a
                    remote reader with no way to raise it sees that a proof was clipped
                    and never sees the rest of it"
            (let [h     (client/handle-of conn (list flies Tweety) CxWire)
                  clipped? (fn clipped? [node]
                             (boolean (or (:truncated? node)
                                          (some (fn [j] (some clipped? (:because j)))
                                                (:support node)))))]
              (is (clipped? (client/why conn h {:max-depth 1})))
              (is (not (clipped? (client/why conn h {:max-depth 32}))))
              (is (thrown? clojure.lang.ExceptionInfo (client/why conn h {:max-dpeth 32}))
                  "and the daemon holds the opts to the same roster the in-process entry point
                   does, rather than taking a default in silence")))
          (testing "a remote refusal surfaces as an ex-info carrying the daemon error"
            (is (thrown? clojure.lang.ExceptionInfo
                         (client/assert conn (list bird '?anything) CxWire))))
          (testing "the deprecated spelling is the same call, which is the whole of what
                    keeping it promises"
            ;; kept because a caller outside this repo may hold it; `!` means
            ;; *irreversible* and an assertion is not, so the wrapper carrying one said
            ;; the opposite of what the entry point does
            #_{:clj-kondo/ignore [:deprecated-var]}
            (let [h (client/assert! conn (list penguin Tweety) CxWire)]
              (is (nat-int? h))
              (is (= h (client/handle-of conn (list penguin Tweety) CxWire)))))
          (testing "retract over the wire tears the fact down"
            (let [h (client/handle-of conn (list bird Tweety) CxWire)]
              (client/retract! conn h)
              (is (empty? (client/sentexes-matching conn (list bird Tweety) CxWire))))))
        (finally
          (.stop server))))))

(tu/deftest-kb the-client-carries-the-token-over-the-socket
  ;; The header half, end to end: `app`'s refusal is exercised without a socket above,
  ;; and what this adds is that the client *sets* the header, on a real request, with
  ;; nothing but the `conn` to carry it.
  (tu/with-terms [bird Tweety CxWire]
    (let [server (serve/start kb {:port 0 :token token})]
      (try
        (let [p        (serve/port server)
              held     (client/client "localhost" p {:token token})
              tokenless (client/client "localhost" p {:token nil})]
          (testing "a client holding the token drives the daemon like any other"
            (is (:ok (client/health held)))
            (is (nat-int? (client/assert held (list bird Tweety) CxWire)))
            (is (= (list bird Tweety)
                   (:sentence (first (client/sentexes-matching held (list bird '?x)
                                                               CxWire))))))
          (testing "and one without it gets the daemon's refusal under the daemon's
                    own :type, the way every other remote refusal arrives"
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (client/ask? tokenless (list bird Tweety) CxWire)))]
              (is (= :unauthorized (:type (ex-data e))))))
          (testing "health is reachable either way — an orchestrator holds no token"
            (is (:ok (client/health tokenless))))
          (testing "a wrong token is the same refusal as none"
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (client/ask? (client/client "localhost" p {:token "nope"})
                                              (list bird Tweety) CxWire)))]
              (is (= :unauthorized (:type (ex-data e)))))))
        (finally
          (.stop server))))))

;; ---- -main's --listen flag ------------------------------------------------

(clojure.test/deftest a-listen-flag-with-no-address-is-refused
  ;; Reading the trailing flag as loopback fails safe and is still a lie: `--listen`
  ;; is the explicit opt-in to a public bind, and an operator whose flag was silently
  ;; ignored walks away believing the daemon is reachable when only this machine can
  ;; see it.  `-main` prints the message and exits 1, the port typo's pattern.
  (testing "absent, the daemon binds loopback"
    (is (= "127.0.0.1" (#'serve/listen-host ["4200" "/tmp/kb"]))))
  (testing "present with an address, it binds that address"
    (is (= "0.0.0.0" (#'serve/listen-host ["4200" "--listen" "0.0.0.0"]))))
  (testing "present with nothing after it, it is refused"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (#'serve/listen-host ["4200" "/tmp/kb" "--listen"])))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= "--listen" (:flag (ex-data e))))
      (is (re-find #"needs an address" (ex-message e)))
      (is (re-find #"line ends after it" (ex-message e)))))
  (testing "and the next flag is not an address — it would bind an interface named
            after a token, which is a Jetty failure rather than this entry point's refusal"
    (doseq [args [["--listen" "--port"] ["4200" "--listen" "--listen" "0.0.0.0"]]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo (#'serve/listen-host args))
                  (pr-str args))]
        (is (= :unknown-option (:type (ex-data e))) (pr-str args))
        (is (re-find #"the next word is the flag" (ex-message e)) (pr-str args))))))

(clojure.test/deftest positionals-survive-a-flag-in-any-position
  ;; A positional silently dropped is a disk daemon running in memory — every client
  ;; write evaporating at exit — so the argument grammar must not depend on where the
  ;; flag sits, and what it does not know it refuses.
  (testing "flags and positionals interleave freely"
    (is (= ["4200" "/var/lib"] (#'serve/positional-args ["4200" "/var/lib" "--listen" "0.0.0.0"])))
    (is (= ["4200" "/var/lib"] (#'serve/positional-args ["4200" "--listen" "0.0.0.0" "/var/lib"])))
    (is (= ["4200" "/var/lib"] (#'serve/positional-args ["--listen" "0.0.0.0" "4200" "/var/lib"]))))
  (testing "an unknown flag is refused, not skipped"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (#'serve/positional-args ["4200" "--lisen" "0.0.0.0"])))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= "--lisen" (:flag (ex-data e))))))
  (testing "a third positional is refused, not ignored"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (#'serve/positional-args ["4200" "/var/lib" "stray"])))]
      (is (= :unknown-option (:type (ex-data e)))))))

(deftest the-parked-poll-ceiling-stays-under-the-thread-pool
  ;; Two numbers that have to stay related, and were not.  A parked long poll holds one
  ;; HTTP worker for the length of its wait, so with the pool implicit at ring's default
  ;; 50 and the subscription ceiling at 64, a caller doing exactly what the feature is
  ;; for could saturate the daemon: 55 parked polls took `/health` from 62 ms to 26 s,
  ;; and one subscription was enough, since nothing bounded polls per token.
  (testing "the pool is stated rather than defaulted, so the pair can be checked at all"
    (is (pos-int? serve/http-threads)))
  (testing "and the parked ceiling leaves the daemon threads to answer everything else"
    (is (< sub/max-parked (quot serve/http-threads 2))
        (str "max-parked " sub/max-parked " must stay well under http-threads "
             serve/http-threads " — a parked poll holds one of them")))
  (testing "every way the daemon is started passes the pool size — `start` and `-main`
            alike, or the command-line daemon runs on Jetty's default and the pair above
            holds for the tests only"
    (let [src   (slurp (io/resource "vaelii/impl/serve.clj"))
          calls (re-seq #"\(jetty/run-jetty[^\n]*\n[^\n]*" src)]
      (is (= 2 (count calls)) "the two starts, and no third that could forget")
      (doseq [c calls]
        (is (re-find #":max-threads http-threads" c) c)))))

(deftest the-client-mirrors-the-daemons-wait-ceiling
  ;; `vaelii.impl.client` carries its own copy rather than requiring the daemon's, which
  ;; would pull the whole engine onto the classpath of a client whose point is not
  ;; needing it.  A mirrored constant drifts unless something says otherwise.
  (is (= sub/max-wait-ms @(resolve 'vaelii.impl.client/max-wait-ms))
      "the client extends its read timeout by what the daemon will actually wait"))
