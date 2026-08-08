;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.guard-test
  "The HTTP guards (`vaelii.impl.guard`) as pure functions — no KB, no socket.

  These pin the refusal paths of the `Host` allowlist that closes DNS rebinding, and
  the pieces it is built from.  The daemon- and browser-level tests
  (`vaelii.serve-test`, `vaelii.web-test`) drive the wrapped handlers; this namespace
  pins the guard's own decisions, including the deliberate carve-outs a handler test
  could mistake for gaps."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.guard :as guard]))

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

(deftest an-any-allowlist-is-the-open-door-it-says-it-is
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
  (if-let [env (System/getenv "VAELII_MAX_BODY_BYTES")]
    (is (= (Long/parseLong env) guard/max-body-bytes)
        "VAELII_MAX_BODY_BYTES names the ceiling")
    (is (= (* 16 1024 1024) guard/max-body-bytes)
        "16 MiB is the ceiling when nothing names another")))
