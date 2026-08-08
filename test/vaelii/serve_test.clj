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
            [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.client :as client]
            [vaelii.impl.guard :as guard]
            [vaelii.impl.serve :as serve]
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
  (tu/with-terms [dog animal Muffet ServeContext]
    (let [handler (open-app kb)]
      (testing "an assert op stores and returns the handle"
        (let [r (post-op handler :assert [(list dog Muffet) ServeContext {:strength :monotonic}])]
          (is (:ok r))
          (is (nat-int? (:result r)))))
      (testing "a query op returns sentex maps — plain, not records"
        (let [r (post-op handler :sentexes-matching [(list dog '?x) ServeContext])]
          (is (:ok r))
          (let [sx (first (:result r))]
            (is (map? sx))
            (is (not (record? sx)) "a record must be projected to a plain map on the wire")
            (is (= (list dog Muffet) (:sentence sx))))))
      (testing "an ask op returns binding maps"
        (v/assert kb (list 'genl dog animal) ServeContext)
        (let [r (post-op handler :ask [(list animal '?x) ServeContext])]
          (is (:ok r))
          (is (some #(= Muffet (get % '?x)) (:result r))
              "specificity: (dog Muffet) answers the (animal ?x) goal")))
      (testing "why returns a proof-tree map"
        (let [h (v/handle-of kb (list dog Muffet) ServeContext)
              r (post-op handler :why [h])]
          (is (:ok r))
          (is (map? (:result r)))
          (is (= (list dog Muffet) (:sentence (:result r))))))
      (testing "preview answers what a batch would believe, and stores nothing"
        ;; served with the writes because it applies the batch and rolls it back — the
        ;; daemon is the single writer, which is exactly the condition it needs
        (tu/with-terms [swims Willy]
          (let [before (tu/sentex-ids kb)
                r (post-op handler :preview
                           [{:add [[(list swims Willy) ServeContext]]}])]
            (is (:ok r))
            (is (= [(list swims Willy)]
                   (mapv :sentence (:believed-added (:result r))))
                "the answer crosses the wire as sentences, not records")
            (is (= before (tu/sentex-ids kb))
                "a preview over the wire stored something")
            (is (nil? (v/handle-of kb (list swims Willy) ServeContext))))))
      (testing "an unknown op is a 400 that lists the real ops"
        (let [r (post-op handler :not-an-op [])]
          (is (false? (:ok r)))
          (is (= 400 (:status r)))
          (is (some #{:assert} (:ops r)))))
      (testing "a refusal (a non-ground fact) comes back as an error, not a crash"
        (let [r (post-op handler :assert [(list dog '?x) ServeContext])]
          (is (false? (:ok r)))
          (is (= :not-ground (:type r)) "the ex-data :type rides the wire")))
      (testing "a non-sequential :args is the caller's mistake — 400 :bad-args with a
                usable :type, not a bare 500 with none"
        (let [r (post-form handler {:op :assert :args 5})]
          (is (= 400 (:status r)))
          (is (false? (:ok r)))
          (is (= :bad-args (:type r))))))))

;; ---- the guards' refusal paths -------------------------------------------

(tu/deftest-kb post-op-refuses-a-cors-simple-content-type
  ;; the CSRF gate: `application/edn` is not a CORS-*simple* type, so a browser must
  ;; preflight it and this daemon answers no preflight — demanding it is what keeps a
  ;; page the operator merely visits from driving the write route
  (tu/with-terms [dog Muffet ServeContext]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)
          refused (fn [headers]
                    (post-op* handler headers :assert [(list dog Muffet) ServeContext]))]
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
        (is (nil? (v/handle-of kb (list dog Muffet) ServeContext)))))))

(tu/deftest-kb post-op-refuses-a-cross-origin-caller
  ;; the other CSRF gate, and the one that bites when a browser *does* stamp an origin:
  ;; `edn-body?` forces a preflight this daemon will not answer, and this refuses the
  ;; page that got one anyway.  A `:type` on the wire because a client discriminating on
  ;; the message string is discriminating on prose.
  (tu/with-terms [dog Muffet ServeContext]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)
          from    (fn [hdrs]
                    (post-op* handler (merge {"content-type" "application/edn"} hdrs)
                              :assert [(list dog Muffet) ServeContext]))]
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
  (tu/with-terms [dog Muffet ServeContext]
    (let [handler (open-app kb)]
      (doseq [ct ["application/edn; charset=utf-8"
                  "Application/EDN"
                  "APPLICATION/EDN; CHARSET=UTF-8"
                  "  application/edn  "]]
        (let [r (post-op* handler {"content-type" ct} :assert
                          [(list dog Muffet) ServeContext])]
          (is (= 200 (:status r)) ct)
          (is (:ok r) ct)))
      (is (some? (v/handle-of kb (list dog Muffet) ServeContext))
          "the accepted spelling reached the op — the fact is stored"))))

(tu/deftest-kb the-daemon-refuses-a-rebound-host-on-every-route
  ;; the DNS-rebinding gate: `same-origin?` folds when the attacker controls both
  ;; `Origin` and `Host` (a domain re-resolving to 127.0.0.1), so `host-allowed?` is
  ;; the check that has to hold — and it wraps the whole server, because a rebound
  ;; page reads the KB as happily as it writes to it
  (tu/with-terms [dog Muffet ServeContext]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)]
      (testing "a write op under a rebound Host is a 400 before anything runs"
        (let [r (post-op* handler {"content-type" "application/edn"
                                   "host"   "evil.example.com"
                                   "origin" "http://evil.example.com"}
                          :assert [(list dog Muffet) ServeContext])]
          (is (= 400 (:status r)))
          (is (false? (:ok r)))
          (is (= :bad-host (:type r)))
          (is (= before (tu/sentex-ids kb)) "the refused op stored nothing")
          (is (nil? (v/handle-of kb (list dog Muffet) ServeContext)))))
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
                          :assert [(list dog Muffet) ServeContext])]
          (is (:ok r))
          (is (nat-int? (:result r)))))
      (testing "and a Host-less request (curl, every other test here) passes by design"
        (is (= 200 (:status (handler {:request-method :get :uri "/health"}))))))))

(tu/deftest-kb export-over-the-wire-writes-on-the-daemons-own-host
  (tu/with-terms [dog Muffet ServeContext]
    (let [handler (open-app kb)
          root (.toFile (Files/createTempDirectory "vaelii-serve-export-"
                                                   (into-array FileAttribute [])))
          dump (java.io.File. root "a-dump")]
      (try
        (v/assert kb (list dog Muffet) ServeContext)
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
  (tu/with-terms [dog Muffet ServeContext]
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
  ;; `serve/ops` itself, so an op added later is covered by construction.
  (let [handler (authed-app kb)]
    (testing "GET /health answers with no credential"
      (let [resp (handler {:request-method :get :uri "/health"})]
        (is (= 200 (:status resp)))
        (is (:ok (edn/read-string (:body resp))))))
    (testing "and every op in the table is refused without one"
      (doseq [op (sort (keys serve/ops))]
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
  ;; length — the two cases a `=` on strings would short-circuit differently.
  (let [matches? #'serve/token-matches?]
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

;; ---- the body ceiling ----------------------------------------------------
;;
;; A caller who can reach `POST /op` is a caller who can spend the daemon's heap by
;; streaming a body at it — and on the open loopback default that is every process on
;; the machine.  The reading half — that the refusal happens *while* reading rather than
;; after — is `vaelii.guard-test`, where the ceiling lives; what belongs here is that the
;; refusal reaches the wire as a 413 in the daemon's own error shape, and that no op ran
;; behind it.

(tu/deftest-kb an-oversized-post-is-a-413-that-runs-no-op
  (tu/with-terms [dog Muffet ServeContext]
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)
          body    (.getBytes ^String (pr-str {:op :assert
                                              :args [(list dog Muffet) ServeContext]})
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
        (is (nil? (v/handle-of kb (list dog Muffet) ServeContext))))
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
  (tu/with-terms [bird flies penguin Tweety WireContext]
    (let [server (serve/start kb {:port 0 :token nil})]
      (try
        (let [conn (client/client "localhost" (serve/port server) {:token nil})]
          (testing "health"
            (is (:ok (client/health conn))))
          (testing "assert / query round-trip over the socket"
            (is (nat-int? (client/assert! conn (list bird Tweety) WireContext)))
            (let [rs (client/sentexes-matching conn (list bird '?x) WireContext)]
              (is (= (list bird Tweety) (:sentence (first rs))))))
          (testing "a forward rule fires server-side and the derived fact is asked back"
            (client/assert-rule! conn [(list bird '?b)] (list flies '?b) WireContext)
            (is (client/ask? conn (list flies Tweety) WireContext)))
          (testing "why over the wire returns a proof tree"
            (let [h (client/handle-of conn (list flies Tweety) WireContext)]
              (is (map? (client/why conn h)))))
          (testing "a remote refusal surfaces as an ex-info carrying the daemon error"
            (is (thrown? clojure.lang.ExceptionInfo
                         (client/assert! conn (list bird '?anything) WireContext))))
          (testing "retract over the wire tears the fact down"
            (let [h (client/handle-of conn (list bird Tweety) WireContext)]
              (client/retract! conn h)
              (is (empty? (client/sentexes-matching conn (list bird Tweety) WireContext))))))
        (finally
          (.stop server))))))

(tu/deftest-kb the-client-carries-the-token-over-the-socket
  ;; The header half, end to end: `app`'s refusal is exercised without a socket above,
  ;; and what this adds is that the client *sets* the header, on a real request, with
  ;; nothing but the `conn` to carry it.
  (tu/with-terms [bird Tweety WireContext]
    (let [server (serve/start kb {:port 0 :token token})]
      (try
        (let [p        (serve/port server)
              held     (client/client "localhost" p {:token token})
              tokenless (client/client "localhost" p {:token nil})]
          (testing "a client holding the token drives the daemon like any other"
            (is (:ok (client/health held)))
            (is (nat-int? (client/assert! held (list bird Tweety) WireContext)))
            (is (= (list bird Tweety)
                   (:sentence (first (client/sentexes-matching held (list bird '?x)
                                                               WireContext))))))
          (testing "and one without it gets the daemon's refusal under the daemon's
                    own :type, the way every other remote refusal arrives"
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (client/ask? tokenless (list bird Tweety) WireContext)))]
              (is (= :unauthorized (:type (ex-data e))))))
          (testing "health is reachable either way — an orchestrator holds no token"
            (is (:ok (client/health tokenless))))
          (testing "a wrong token is the same refusal as none"
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (client/ask? (client/client "localhost" p {:token "nope"})
                                              (list bird Tweety) WireContext)))]
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
      (is (re-find #"needs an address" (ex-message e))))))

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
