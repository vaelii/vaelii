;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.guard-test
  "The HTTP guards (`vaelii.host.guard`) as pure functions — no KB, no socket.

  These pin the refusal paths of the `Host` allowlist that closes DNS rebinding, and
  the pieces it is built from.  The daemon- and browser-level tests
  (`vaelii.serve-test`, `vaelii.web-test`) drive the wrapped handlers; this namespace
  pins the guard's own decisions, including the deliberate carve-outs a handler test
  could mistake for gaps."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.host.guard :as guard]))

(def ^:private strip-port #'guard/strip-port)

;; ---- strip-port ----------------------------------------------------------

(deftest strip-port-reads-the-host-part
  (testing "a plain host:port loses the port"
    (is (= "localhost" (strip-port "localhost:3000")))
    (is (= "127.0.0.1" (strip-port "127.0.0.1:4200")))
    (is (= "evil.example.com" (strip-port "evil.example.com:3000"))))
  (testing "no port, nothing stripped"
    (is (= "localhost" (strip-port "localhost")))
    (is (= "127.0.0.1" (strip-port "127.0.0.1"))))
  (testing "a bracketed IPv6 literal keeps its brackets and loses the port"
    (is (= "[::1]" (strip-port "[::1]:3000")))
    (is (= "[::1]" (strip-port "[::1]"))))
  (testing "a bare IPv6 literal has no port to strip — the colons are the address"
    (is (= "::1" (strip-port "::1")))
    (is (= "0:0:0:0:0:0:0:1" (strip-port "0:0:0:0:0:0:0:1"))))
  (testing "an unclosed bracket is left whole, so the allowlist lookup fails closed"
    (is (= "[::1" (strip-port "[::1")))))

;; ---- allowed-hosts -------------------------------------------------------

(deftest allowed-hosts-follows-the-bind
  ;; `VAELII_ALLOWED_HOSTS` overrides both branches, and `System/getenv` is a static
  ;; call with no var to fake — so this asserts the default branches, and skips when
  ;; the environment carries the override (under it, the defaults are genuinely not
  ;; in force).  The override's *consumption* is pinned below through `host-allowed?`,
  ;; which takes the set as a value.
  (if (some? (System/getenv "VAELII_ALLOWED_HOSTS"))
    (println "SKIP vaelii.guard-test/allowed-hosts-follows-the-bind:"
             "VAELII_ALLOWED_HOSTS is set in this environment")
    (do
      (testing "a loopback bind answers only to loopback spellings"
        (is (= guard/loopback-hosts (guard/allowed-hosts "127.0.0.1")))
        (is (= guard/loopback-hosts (guard/allowed-hosts "localhost")))
        (is (= guard/loopback-hosts (guard/allowed-hosts "::1")))
        (is (= guard/loopback-hosts (guard/allowed-hosts "[::1]"))))
      (testing "the bind's own case does not matter"
        (is (= guard/loopback-hosts (guard/allowed-hosts "LocalHost"))))
      (testing "a non-loopback bind is an explicit operator choice and is left open"
        (is (= ::guard/any (guard/allowed-hosts "0.0.0.0")))
        (is (= ::guard/any (guard/allowed-hosts "192.168.1.5")))))))

(deftest an-allowlist-entry-is-read-in-the-shape-a-host-header-is-compared-in
  ;; `host-allowed?` strips the port off the request's `Host`, so an entry that keeps one
  ;; matches nothing at all — every request refused, while the startup line reports the
  ;; allowlist as set.  Driven through the parser rather than the reader, since
  ;; `System/getenv` is a static call with no var to fake.
  (let [parse #'guard/parse-allowlist]
    (testing "a port on an entry is the name it is written beside"
      (is (= #{"kb.example.com"} (parse "kb.example.com:8080")))
      (is (= #{"kb.example.com"} (parse "kb.example.com")))
      (is (= #{"[::1]"} (parse "[::1]:4200")))
      (is (= #{"::1"} (parse "::1")) "a bare IPv6 literal has no port to strip"))
    (testing "and the entry parsed is what host-allowed? then compares against"
      (is (guard/host-allowed? (parse "kb.example.com:8080")
                               {:headers {"host" "kb.example.com:8080"}}))
      (is (guard/host-allowed? (parse "kb.example.com:8080")
                               {:headers {"host" "kb.example.com"}}))
      (is (not (guard/host-allowed? (parse "kb.example.com:8080")
                                    {:headers {"host" "evil.example"}}))))
    (testing "several entries, trimmed and case-folded as header values are"
      (is (= #{"kb.example.com" "kb.internal"}
             (parse " KB.Example.com:443 , kb.internal "))))
    (testing "a value naming nothing is unset, not an allowlist of none — the empty set
              answers no Host on any interface"
      (is (nil? (parse nil)))
      (is (nil? (parse "")))
      (is (nil? (parse "   ")))
      (is (nil? (parse " , , "))))))

;; ---- allowlist-open? -------------------------------------------------------

(deftest allowlist-open-names-the-one-sentinel
  (testing "the ::any sentinel, and only it, reads as open"
    (is (true?  (guard/allowlist-open? ::guard/any)))
    (is (false? (guard/allowlist-open? guard/loopback-hosts)))
    (is (false? (guard/allowlist-open? #{"kb.example.com"})))
    (is (false? (guard/allowlist-open? #{})))))

;; ---- host-allowed? -------------------------------------------------------

(deftest host-allowed-refuses-a-rebound-name-on-a-loopback-bind
  (let [allowed guard/loopback-hosts               ; what a loopback bind yields
        req     (fn [host] {:headers {"host" host}})]
    (testing "a name that re-resolved to 127.0.0.1 is exactly what is refused"
      (is (not (guard/host-allowed? allowed (req "evil.example.com"))))
      (is (not (guard/host-allowed? allowed (req "evil.example.com:3000")))))
    (testing "an unknown name fails closed — the set says what is allowed, not what is blocked"
      (is (not (guard/host-allowed? allowed (req "kb.internal")))))
    (testing "every loopback spelling passes, with or without a port"
      (is (guard/host-allowed? allowed (req "localhost")))
      (is (guard/host-allowed? allowed (req "localhost:3000")))
      (is (guard/host-allowed? allowed (req "127.0.0.1:4200")))
      (is (guard/host-allowed? allowed (req "[::1]:3000")))
      (is (guard/host-allowed? allowed (req "::1"))))
    (testing "matching is case-insensitive and whitespace-tolerant, as header values are"
      (is (guard/host-allowed? allowed (req "LOCALHOST:3000")))
      (is (guard/host-allowed? allowed (req " localhost "))))))

(deftest a-request-with-no-host-is-allowed-by-design
  ;; the deliberate carve-out: HTTP/1.1 requires `Host` and every browser sends it,
  ;; so its absence marks a non-browser client (curl, a test's request map) — which
  ;; has no ambient browser context to ride, and is not the request rebinding is
  ;; about.  Pinned so any future tightening is a visible choice, not drift.
  (is (guard/host-allowed? guard/loopback-hosts {}))
  (is (guard/host-allowed? guard/loopback-hosts {:headers {}})))

(deftest an-any-allowlist-is-the-open-entry-point-it-says-it-is
  ;; the non-loopback-bind branch: an operator who bound an address reaches the
  ;; server under a name only they know, so nothing is guessed at
  (is (guard/host-allowed? ::guard/any {:headers {"host" "evil.example.com"}})))

(deftest an-override-allowlist-is-consumed-verbatim
  ;; the set `VAELII_ALLOWED_HOSTS=kb.example.com` produces (`allowed-hosts`
  ;; lower-cases each entry), driven through the check that reads it
  (let [allowed #{"kb.example.com"}]
    (is (guard/host-allowed? allowed {:headers {"host" "kb.example.com:4200"}}))
    (is (guard/host-allowed? allowed {:headers {"host" "KB.Example.COM"}}))
    (is (not (guard/host-allowed? allowed {:headers {"host" "localhost"}}))
        "an override replaces the loopback set rather than adding to it")))

;; ---- wrap-host-allowed ---------------------------------------------------

(deftest wrap-host-allowed-refuses-before-the-handler-runs
  (let [ran     (atom 0)
        handler (fn [_] (swap! ran inc) {:status 200 :body "ok"})
        refusal (fn [_] {:status 400 :body "no"})
        wrapped (guard/wrap-host-allowed handler guard/loopback-hosts refusal)]
    (testing "a bad host gets the refusal and the wrapped handler never runs"
      (is (= 400 (:status (wrapped {:headers {"host" "evil.example.com"}}))))
      (is (zero? @ran)))
    (testing "a good host reaches the handler"
      (is (= 200 (:status (wrapped {:headers {"host" "localhost:3000"}}))))
      (is (= 1 @ran)))))

;; ---- edn-body? -----------------------------------------------------------

(deftest edn-body-prefix-matches-the-declared-type
  ;; the CSRF gate's own decision, at the pure level; the daemon-level consequences
  ;; (415, no side effect) are `vaelii.serve-test`'s
  (let [req (fn [ct] {:headers {"content-type" ct}})]
    (testing "parameters and case variants still declare EDN"
      (is (guard/edn-body? (req "application/edn")))
      (is (guard/edn-body? (req "application/edn; charset=utf-8")))
      (is (guard/edn-body? (req "Application/EDN")))
      (is (guard/edn-body? (req "  application/edn  "))))
    (testing "the three CORS-simple types — what a cross-site fetch can send without a
              preflight — are exactly what is refused"
      (is (not (guard/edn-body? (req "text/plain"))))
      (is (not (guard/edn-body? (req "application/x-www-form-urlencoded"))))
      (is (not (guard/edn-body? (req "multipart/form-data")))))
    (testing "no declaration at all is refused too"
      (is (not (guard/edn-body? {})))
      (is (not (guard/edn-body? {:headers {}}))))))

;; ---- what a bind requires ------------------------------------------------
;;
;; One rule for both servers: naming an address publishes write routes that authenticate
;; nobody, and the same flag drops the `Host` allowlist — so the exposed configuration
;; must not also be the one with the fewest checks.  `vaelii.serve-test` and
;; `vaelii.web-test` drive each server's own entry point; what belongs here is the
;; decision itself.

(deftest a-public-bind-is-every-interface-that-is-not-this-machine
  (testing "loopback, however it is spelled"
    (doseq [h ["127.0.0.1" "localhost" "[::1]" "::1" "0:0:0:0:0:0:0:1" "LOCALHOST"]]
      (is (false? (guard/public-bind? h)) h)))
  (testing "and anything else"
    (doseq [h ["0.0.0.0" "::" "10.0.0.4" "example.internal"]]
      (is (true? (guard/public-bind? h)) h))))

(deftest an-address-with-no-token-is-refused-naming-the-variable
  (testing "loopback needs none — the laptop workflow a required credential would
            only teach an operator to export a constant for"
    (doseq [h ["127.0.0.1" "localhost" "::1"]]
      (is (nil? (guard/require-token! "daemon" h nil)) h))
    (is (nil? (guard/require-token! "daemon" "127.0.0.1" "  "))
        "a blank token is an unset one, and loopback does not need one"))
  (testing "a token satisfies either bind"
    (is (nil? (guard/require-token! "daemon" "0.0.0.0" "s3cret")))
    (is (nil? (guard/require-token! "browser" "10.0.0.4" "s3cret"))))
  (testing "and an address with none is refused, naming what lifts it and what avoids it"
    (doseq [[what h] [["daemon" "0.0.0.0"] ["browser" "10.0.0.4"] ["browser" "::"]]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo (guard/require-token! what h nil))
                  (str what " " h))]
        (is (= :unauthorized (:type (ex-data e))) h)
        (is (= h (:host (ex-data e))) h)
        (is (= what (:server (ex-data e))) h)
        (is (re-find #"VAELII_API_TOKEN" (ex-message e)) h)
        (is (re-find #"loopback" (ex-message e)) h)))))

(deftest the-bearer-wrapper-answers-one-refusal-however-the-header-is-wrong
  (let [seen    (atom 0)
        handler (guard/wrap-bearer (fn [_] (swap! seen inc) :served)
                                   "s3cret" #{"/health"} (fn [_] :refused))
        get*    (fn [uri headers] (handler {:request-method :get :uri uri
                                            :headers headers}))]
    (testing "the right token is served"
      (is (= :served (get* "/" {"authorization" "Bearer s3cret"})))
      (is (= :served (get* "/" {"authorization" "bearer s3cret"}))
          "the scheme is matched case-insensitively, as RFC 7235 defines it"))
    (testing "and every way of not having it takes the same branch"
      (doseq [h [{} {"authorization" ""} {"authorization" "Bearer wrong"}
                 {"authorization" "Basic s3cret"} {"authorization" "s3cret"}]]
        (is (= :refused (get* "/" h)) (pr-str h))))
    (testing "an open route answers before the check"
      (is (= :served (get* "/health" {}))))
    (testing "a blank token means no wrapper at all"
      (let [open (guard/wrap-bearer (fn [_] :served) "" #{} (fn [_] :refused))]
        (is (= :served (open {:request-method :get :uri "/"})))))
    (is (= 3 @seen)
        "the wrapped handler ran for the two good tokens and the open route, and for
         nothing else — a refusal is answered before the handler, not after it")))

;; ---- the request-body ceiling --------------------------------------------
;;
;; The browser authenticates nobody and the daemon need not, so the caller who can reach
;; a write route is the caller who can spend the process's heap by streaming a body at
;; it.  What has to hold is not
;; only that an oversized body is refused but that it is refused **while being read** —
;; a ceiling checked after the read is the read it was meant to prevent.  The two
;; servers' 413s are `vaelii.serve-test` and `vaelii.web-test`; this is the reading
;; itself.

(defn- bytes-in
  "A request whose body is `n` bytes, on a stream that reports what is left of it."
  [n]
  {:body (java.io.ByteArrayInputStream. (byte-array n))})

(deftest a-body-past-the-ceiling-is-refused-instead-of-slurped
  (let [size  (* 512 1024)
        limit (* 64 1024)
        req   (bytes-in size)
        ^java.io.ByteArrayInputStream in (:body req)
        e     (with-redefs [guard/max-body-bytes limit]
                (try (guard/read-capped-body-bytes req) nil
                     (catch clojure.lang.ExceptionInfo ex ex)))]
    (is (some? e) "an oversized body was read to the end and handed back")
    (is (= :body-too-large (:type (ex-data e))) "one refusal type for both servers")
    (is (= limit (:limit (ex-data e))) "and it says which ceiling it hit")
    (testing "it stopped reading, which is the whole difference from slurp"
      (is (pos? (.available in))
          "the body was drained: a ceiling checked after the read is not a ceiling")
      ;; the ceiling is checked before the chunk is written, so the reader stops with at
      ;; most one chunk past it in hand — exactly one when the limit is a whole number of
      ;; chunks, as it is here
      (is (<= (- size (.available in)) (+ limit 8192))
          "more than one chunk past the ceiling was read before it gave up"))
    (testing "a body under the ceiling comes back whole, and as UTF-8 on the string arm"
      (with-redefs [guard/max-body-bytes limit]
        (let [body (.getBytes "(dog Muffet) — é" "UTF-8")]
          (is (= (seq body)
                 (seq (guard/read-capped-body-bytes
                       {:body (java.io.ByteArrayInputStream. body)}))))
          (is (= "(dog Muffet) — é"
                 (guard/read-capped-body
                  {:body (java.io.ByteArrayInputStream. body)}))))))
    (testing "and a request carrying no body at all is empty, not a crash"
      (is (zero? (alength (guard/read-capped-body-bytes {}))))
      (is (= "" (guard/read-capped-body {}))))))

(deftest wrap-body-limit-refuses-before-the-handler-runs
  (let [ran     (atom 0)
        seen    (atom nil)
        handler (fn [req]
                  (swap! ran inc)
                  (reset! seen (slurp (:body req)))
                  {:status 200 :body "ok"})
        refusal (fn [_] {:status 413 :body "too large"})
        wrapped (guard/wrap-body-limit handler refusal)]
    (testing "past the ceiling the wrapped handler never runs"
      (let [r (with-redefs [guard/max-body-bytes 8]
                (wrapped {:body (java.io.ByteArrayInputStream. (.getBytes "0123456789" "UTF-8"))}))]
        (is (= 413 (:status r)))
        (is (zero? @ran))))
    (testing "under it the handler runs and its body is still readable — the buffered
              copy is what a params middleware downstream then reads, and a consumed
              stream would leave it with an empty form"
      (let [r (wrapped {:body (java.io.ByteArrayInputStream. (.getBytes "a=1&b=2" "UTF-8"))})]
        (is (= 200 (:status r)))
        (is (= 1 @ran))
        (is (= "a=1&b=2" @seen))))
    (testing "and a request with no body at all passes through"
      (is (= 200 (:status (wrapped {}))))
      (is (= 2 @ran)))))

(deftest the-ceiling-is-sixteen-mebibytes-unless-the-environment-moves-it
  ;; A daemon op body is a sentence and its context and a browser body is a form, so
  ;; 16 MiB is nowhere near a legitimate call and the number is a contract rather than a
  ;; tuning knob.  `VAELII_MAX_BODY_BYTES` is the operator's override and is read once,
  ;; at load, so what is answerable in-process is that the value agrees with the
  ;; environment this JVM was started in — either way round.
  (if-let [env (some-> (System/getenv "VAELII_MAX_BODY_BYTES") .trim not-empty)]
    (is (= (Long/parseLong env) guard/max-body-bytes)
        "VAELII_MAX_BODY_BYTES names the ceiling")
    (is (= (* 16 1024 1024) guard/max-body-bytes)
        "16 MiB is the ceiling when nothing names another")))

(deftest a-blank-ceiling-is-unset-and-a-bad-one-names-the-switch
  ;; `VAELII_MAX_BODY_BYTES=` exported empty is the shell saying nothing, as it is for every
  ;; other switch; read as a value it refused guard's load, which is both servers' start.
  (doseq [raw [nil "" "   "]]
    (is (= (* 16 1024 1024) (#'guard/body-ceiling raw)) (str (pr-str raw) " is unset")))
  (is (= 2000 (#'guard/body-ceiling " 2000 ")))
  (doseq [raw ["16m" "0" "-1"]]
    (let [d (try (#'guard/body-ceiling raw) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= [:unknown-option "VAELII_MAX_BODY_BYTES"] ((juxt :type :switch) d))
          (str (pr-str raw) " is refused, naming the switch")))))

;; ---- same-origin? --------------------------------------------------------

(deftest same-origin-honors-a-forwarded-scheme-behind-a-tls-proxy
  (let [;; a request the browser sent as https, reaching the daemon over a plain
        ;; connector behind a TLS-terminating proxy: the connector's :scheme is :http
        req (fn [{:keys [origin host xfp scheme]}]
              {:scheme  (or scheme :http)
               :headers (cond-> {}
                          origin (assoc "origin" origin)
                          host   (assoc "host" host)
                          xfp    (assoc "x-forwarded-proto" xfp))})]
    (testing "the browser's https Origin matches through X-Forwarded-Proto"
      (is (guard/same-origin?
           (req {:origin "https://kb.example.com" :host "kb.example.com"
                 :xfp "https" :scheme :http})))
      (testing "even when the proxy appends a list, the first value wins"
        (is (guard/same-origin?
             (req {:origin "https://kb.example.com" :host "kb.example.com"
                   :xfp "https, http" :scheme :http})))))
    (testing "a cross-site Origin is still refused — the forwarded header cannot forge it"
      (is (not (guard/same-origin?
                (req {:origin "https://evil.example.com" :host "kb.example.com"
                      :xfp "https" :scheme :http})))))
    (testing "with no proxy header, the connector's own scheme decides, as before"
      (is (guard/same-origin?
           (req {:origin "http://localhost:3000" :host "localhost:3000" :scheme :http})))
      (is (not (guard/same-origin?
                (req {:origin "https://localhost:3000" :host "localhost:3000" :scheme :http})))
          "an https Origin with no forwarded proto over a plain connector does not match"))
    (testing "a request carrying neither Origin nor Referer is same-origin by default"
      (is (guard/same-origin? (req {:host "kb.example.com" :scheme :http}))))))
