;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.guard
  "The HTTP guards both servers hold to — `vaelii.browser.web` (the browser) and
  `vaelii.host.serve` (the daemon).

  The browser authenticates nobody and the daemon only when a token is set
  (`api-token`), and both bind loopback for that reason.  Loopback is what makes the
  checks here necessary rather than sufficient: a browser running on the same machine
  *is* a local client, so \"only this machine may reach it\" does not mean \"only this
  machine's owner may drive it\".  Two attacks follow from that, and each guard below
  closes one.

  **Cross-site request forgery.**  Any page the operator visits can `fetch` a loopback
  URL.  `same-origin?` rejects the write whenever the browser stamps `Origin`.
  `edn-body?` closes the case where it does not: `application/edn` is not a
  CORS-*simple* content type, so a browser must preflight it, and a server answering
  no CORS headers fails that preflight before the request is ever sent.

  **DNS rebinding.**  `same-origin?` compares `Origin` against the request's own
  `Host`, so an attacker controlling both — a domain that re-resolves to 127.0.0.1
  once the page is loaded — satisfies it.  `host-allowed?` is the check that does not
  fold, because the `Host` header must then name the interface the server was actually
  started on."
  (:require [clojure.string :as str]))

(def loopback-hosts
  "The `Host` values that name this machine.  Both bracketed and bare IPv6 spellings,
  since a client picks either."
  #{"localhost" "127.0.0.1" "[::1]" "::1"
    "0:0:0:0:0:0:0:1" "[0:0:0:0:0:0:0:1]"})

(defn- strip-port
  "The host part of a `Host` header value.  An IPv6 literal is bracketed when it
  carries a port (RFC 3986), so the bracket — not the last colon — is what delimits
  it; a bare `::1` has no port to strip at all."
  [^String h]
  (cond
    (str/starts-with? h "[") (if-let [c (str/index-of h "]")] (subs h 0 (inc c)) h)
    (> (count (re-seq #":" h)) 1) h
    :else (if-let [c (str/index-of h ":")] (subs h 0 c) h)))

(defn- parse-allowlist
  "The host names a `VAELII_ALLOWED_HOSTS` value names, as the set `host-allowed?`
  compares a request's `Host` against — or **nil** when it names none.

  Each entry gets the same `strip-port` the request side gets, so the two are compared in
  one shape: an operator writes the name they reach the server by, and
  `kb.example.com:8080` left unstripped matches nothing at all — every request refused,
  while the startup line reports the allowlist as set.

  Nil rather than the empty set for a value that names nothing, because those are
  different answers: an empty allowlist admits no `Host` on any interface, and a
  whitespace-only variable is the shell saying nothing rather than an operator asking for
  a server that refuses every request."
  [raw]
  (not-empty
   (into #{} (comp (map str/trim)
                   (remove str/blank?)
                   (map str/lower-case)
                   (map strip-port))
         (str/split (str raw) #","))))

(defn allowed-hosts
  "The allowlist for a server bound to `bound-host`.

  `VAELII_ALLOWED_HOSTS` (comma-separated **host names**) overrides everything; an entry
  carrying a port is read as the name alone, since that is what a `Host` header is
  compared as, and a value naming nothing at all is unset.  Otherwise a
  loopback bind — the default — answers only to loopback names, which is what closes
  rebinding.  A bind that named an address is already an explicit choice made against
  a documented warning, and the operator reaches it under a name only they know, so
  it is left open rather than guessed at — refusing it would trip a daemon fronted by
  a reverse proxy that legitimately sets its own `Host`, which the operator cannot
  always enumerate in advance.  Left unset, `serve`'s startup line warns once rather
  than staying silent about it (`allowlist-open?`)."
  [bound-host]
  (or (parse-allowlist (System/getenv "VAELII_ALLOWED_HOSTS"))
      (when (contains? loopback-hosts (str/lower-case (str bound-host)))
        loopback-hosts)
      ::any))

(defn allowlist-open?
  "Does `allowed` — as `allowed-hosts` returns it — admit every `Host`?  True only for
  a public bind with no `VAELII_ALLOWED_HOSTS`: the loopback default and any
  `VAELII_ALLOWED_HOSTS` value both resolve to a concrete set instead.  What a caller
  above this namespace uses to turn the sentinel into an operator-facing word — `serve`'s
  startup line names the posture rather than logging the keyword."
  [allowed]
  (= allowed ::any))

(defn host-allowed?
  "Does this request's `Host` name an interface `allowed` covers?

  A request carrying **no** `Host` is allowed: HTTP/1.1 requires the header and every
  browser sends it, so its absence marks a non-browser client (curl, a test's request
  map) — which has no ambient browser context to ride, and is not the request
  rebinding is about.  Same carve-out `same-origin?` makes, for the same reason."
  [allowed req]
  (or (= allowed ::any)
      (if-let [h (get-in req [:headers "host"])]
        (contains? allowed (str/lower-case (strip-port (str/trim h))))
        true)))

(defn url-origin
  "The `scheme://authority` a URL names, or `::opaque` when it names none — a
  sandboxed frame sends `Origin: null`, which is a real origin claim that matches
  nothing and must not be read as \"no header\"."
  [url]
  (or (try (let [u (java.net.URI. (str url))]
             (when (and (.getScheme u) (.getAuthority u))
               (str (.getScheme u) "://" (.getAuthority u))))
           (catch Exception _ nil))
      ::opaque))

(defn- request-scheme
  "The scheme the **browser** reached this site by, honoring a TLS-terminating reverse
  proxy: the first value of `X-Forwarded-Proto` when a proxy set one, else the
  connector's own `:scheme`.  Reading an untrusted header is safe **here**: it only
  reconstructs the host side of an origin comparison whose security rests on the
  browser's unforgeable `Origin` — forging the proto cannot forge a matching `Origin`,
  and a non-browser client that controls both is not the cross-site threat this guards.
  Without it, a daemon behind the TLS proxy the deployment docs prescribe sees every
  write as `http` against an `https` `Origin` and refuses all of them."
  [req]
  (or (some-> (get-in req [:headers "x-forwarded-proto"])
              (str/split #",") first str/trim str/lower-case not-empty)
      (name (:scheme req :http))))

(defn same-origin?
  "Does this request come from the browser's own copy of this site?  A write route
  with no session to authenticate has to ask **who asked**: a browser stamps `Origin`
  (falling back to `Referer`) on a form or fetch POST and a page on another site
  cannot forge it, so comparing it to the request's own `Host` rejects a cross-site
  write while leaving the browser's own pages alone.

  A request carrying **neither** header is same-origin by default: that is a
  non-browser client, which has no ambient browser context for another site to ride.
  It is `host-allowed?` that keeps this from being the whole story — on its own this
  check folds under DNS rebinding, where both headers are the attacker's."
  [req]
  (if-let [claimed (some #(get-in req [:headers %]) ["origin" "referer"])]
    (= (url-origin claimed)
       (when-let [host (get-in req [:headers "host"])]
         (str (request-scheme req) "://" host)))
    true))

(defn edn-body?
  "Is this request's body declared `application/edn`?

  The daemon requires it, and the requirement is a CSRF guard rather than a parsing
  one: the three content types a cross-site `fetch` may set without a preflight are
  `text/plain`, `application/x-www-form-urlencoded` and `multipart/form-data`, so
  demanding anything else forces a preflight the daemon cannot answer."
  [req]
  (-> (get-in req [:headers "content-type"] "")
      str/trim
      str/lower-case
      (str/starts-with? "application/edn")))

(defn wrap-host-allowed
  "Wrap `handler` so a request whose `Host` falls outside `allowed` gets `refusal`
  instead.  Applied to the whole server rather than to its write routes: a rebound
  page reads as well as it writes, and the KB is what it came for."
  [handler allowed refusal]
  (fn [req]
    (if (host-allowed? allowed req)
      (handler req)
      (refusal req))))

;; ---- the shared bearer token --------------------------------------------

(defn api-token
  "The daemon's shared bearer token, `VAELII_API_TOKEN`, or nil when it is unset or
  blank.

  **Read here rather than at either end of the wire**, for `max-body-bytes`' reason:
  the daemon that requires the token and the client that presents it are two readers of
  one variable, and two readings of \"set\" is one of them wrong.  A whitespace-only
  value is *unset* — an exported-but-empty variable is the shell's way of saying
  nothing — and anything else is the token byte for byte, untrimmed, because trimming a
  secret silently changes it.

  An environment variable rather than an option or a file: it is what a process manager
  injects without the value reaching the repo, and nothing that reads a KB's opts can
  leak it into a store."
  []
  (let [v (System/getenv "VAELII_API_TOKEN")]
    (when-not (str/blank? v) v)))

;; ---- what a bind requires ------------------------------------------------

(defn public-bind?
  "Does `host` name an interface other than this machine's own?  Membership in
  `loopback-hosts` rather than equality with one spelling of it, so the bind that
  requires a token is exactly the bind that drops the `Host` allowlist:
  `--listen 127.0.0.1` is the default said out loud and is held to the loopback rule,
  `--listen 0.0.0.0` is not."
  [host]
  (not (contains? loopback-hosts (str/lower-case (str host)))))

(defn require-token!
  "Refuse (`:unauthorized`) a **public** bind with no token, naming the variable that
  lifts the refusal and the bind that does not need one.  Returns nil for a loopback
  bind and for a public bind that has a token.

  **One rule for both servers**, because both have write routes and neither
  authenticates by default: the daemon's `POST /op` is the KB's only writer, and the
  browser's `/edit` writes belief while `/kbs/export` and `/kbs/load` write the host
  filesystem at a path the request names.  Naming an address also drops the `Host`
  allowlist (`allowed-hosts`), so without this the exposed configuration would be the
  one with the fewest checks — which is the whole argument, and it is the same argument
  on either server.

  `what` names the server in the message, since an operator reading one line on stderr
  has only the message to go on."
  [what host token]
  (when (and (public-bind? host) (str/blank? token))
    (throw (ex-info (str "VAELII_API_TOKEN must be set to bind " host " — naming an"
                         " address publishes the " what "'s write routes, and they"
                         " authenticate nobody without it.  Set the variable, or bind"
                         " loopback (the default, and what --listen 127.0.0.1 says out"
                         " loud), which answers only this machine")
                    {:type :unauthorized :host host :server what}))))

;; ---- the shared bearer token, on the wire --------------------------------

(defn bearer-matches?
  "Is `presented` the `expected` token?  Compared in **constant time**:
  `MessageDigest/isEqual` folds the length difference into its accumulator and reads
  every byte either way, so neither the token's length nor the prefix a guess shares
  with it shows up in how long the answer takes.  `=` on strings leaks both, and a
  refusal that returns faster for a wrong first byte is a token oracle a caller can
  walk.

  No timing test asserts this, deliberately: a wall-clock assertion over a nanosecond
  difference is flaky by construction on a machine running anything else.  What is
  testable is that one named fn does the comparison and answers correctly for equal- and
  unequal-length inputs, which is why the comparison lives here rather than inline in the
  wrapper below — and why it lives *here* rather than in either server: two spellings of
  a credential comparison is one of them wrong."
  [expected presented]
  (java.security.MessageDigest/isEqual
   (.getBytes (str expected) java.nio.charset.StandardCharsets/UTF_8)
   (.getBytes (str presented) java.nio.charset.StandardCharsets/UTF_8)))

(defn presented-bearer-token
  "The token an `Authorization: Bearer …` header carries, or nil when the header is
  absent or names another scheme.  The scheme is matched case-insensitively, as RFC
  7235 defines it, and the token's own case is kept."
  [req]
  (let [auth (str (get-in req [:headers "authorization"]))]
    (when (str/starts-with? (str/lower-case auth) "bearer ")
      (subs auth 7))))

(defn wrap-bearer
  "Wrap `handler` so every request presents `token` as `Authorization: Bearer <token>`,
  answering `refusal` (a fn of the request) when it does not.  A blank token means no
  wrapper at all.  `open` is the set of request URIs answered before the check.

  **The refusal does not distinguish.**  A wrong token, a missing header and a header
  spelled some other way take the *same* branch: one that said which is a token oracle.

  **Outermost**, outside the `Host` allowlist and the origin check: a caller with no
  token is answered before the server forms any other opinion about the request."
  [handler token open refusal]
  (if (str/blank? token)
    handler
    (fn [req]
      (if (or (contains? open (:uri req))
              (when-let [presented (presented-bearer-token req)]
                (bearer-matches? token presented)))
        (handler req)
        (refusal req)))))

;; ---- the request-body ceiling -------------------------------------------

(def max-body-bytes
  "The cap on a request body, `VAELII_MAX_BODY_BYTES` or 16 MiB.

  The browser authenticates nobody and the daemon need not, so an unbounded body is
  heap an anonymous caller can spend by streaming one — and the legitimate bodies are
  tiny either side: the daemon's is a sentence and its context, the browser's is a
  form.  **One constant and one variable for both**, because two servers with two
  ceilings is one of them wrong, and an operator who lowers the limit means the machine
  rather than a route.

  A value that is not a positive integer is **refused at load**, naming itself.  This
  namespace is read by both servers, so a silent fallback would leave an operator who
  meant `16m` believing a cap they never set — and a raw `NumberFormatException` out of
  a `def` reports as a namespace that would not load rather than as the typo it is."
  (if-let [raw (System/getenv "VAELII_MAX_BODY_BYTES")]
    (let [n (try (Long/parseLong (str/trim raw))
                 (catch NumberFormatException _
                   (throw (ex-info (str "VAELII_MAX_BODY_BYTES is not a number: "
                                        (pr-str raw) " — want a byte count")
                                   {:type :unknown-option :mismatch :bad-value :value raw}))))]
      (when-not (pos? n)
        (throw (ex-info (str "VAELII_MAX_BODY_BYTES must be positive, got " n
                             " — a zero or negative ceiling refuses every request")
                        {:type :unknown-option :mismatch :bad-value :value raw})))
      n)
    (* 16 1024 1024)))

(defn- too-large!
  "The one refusal both servers' 413s are built from, so the wire `:type` is the same
  whichever answered."
  []
  (throw (ex-info (str "request body exceeds " max-body-bytes
                       " bytes — send less, or raise VAELII_MAX_BODY_BYTES")
                  {:type :body-too-large :limit max-body-bytes})))

(defn read-capped-body-bytes
  "`req`'s body as a byte array, refusing past `max-body-bytes`.  `slurp` — and ring's
  own params middleware — read an unbounded body into the heap before anything gets to
  look at it, which is the whole of what this replaces."
  ^bytes [req]
  (if-let [^java.io.InputStream in (:body req)]
    (let [out   (java.io.ByteArrayOutputStream.)
          chunk (byte-array 8192)]
      (loop []
        (let [n (.read in chunk)]
          (when (pos? n)
            (when (> (+ (.size out) n) max-body-bytes) (too-large!))
            (.write out chunk 0 n)
            (recur))))
      (.toByteArray out))
    (byte-array 0)))

(defn read-capped-body
  "`req`'s body as a UTF-8 string, refusing past `max-body-bytes`."
  ^String [req]
  (String. (read-capped-body-bytes req) java.nio.charset.StandardCharsets/UTF_8))

(defn wrap-body-limit
  "Wrap `handler` so a request body past `max-body-bytes` gets `refusal` (a fn of the
  request) instead — the 413.

  For a server that does **not** read its own bodies.  The browser reads its forms
  through ring's params middleware, which slurps the body itself and has no ceiling, so
  the cap has to be applied outside it; the buffered copy this leaves on `:body` is what
  that middleware then reads.  The daemon reads its own body and calls
  `read-capped-body` directly."
  [handler refusal]
  (fn [req]
    (let [body (try (read-capped-body-bytes req)
                    (catch clojure.lang.ExceptionInfo e
                      (if (= :body-too-large (:type (ex-data e)))
                        ::over
                        (throw e))))]
      (if (= ::over body)
        (refusal req)
        (handler (assoc req :body (java.io.ByteArrayInputStream. ^bytes body)))))))
