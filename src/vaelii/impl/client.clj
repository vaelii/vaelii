;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.client
  "A thin EDN-over-HTTP client for the vaelii daemon (`vaelii.impl.serve`).  Runs no
  engine: it POSTs `{:op :args}` and reads the result back, over JDK `java.net.http`
  (no dependency — JDK 21 ships it).

  Every call threads an **explicit connection handle** as its first argument —
  `(query conn '(dog ?x) 'Ctx)` — the network mirror of `vaelii.core`'s explicit-`kb`
  API.  A `conn` from `client` holds a reusable `HttpClient`; no socket opens until a
  call.  A daemon reply of `{:ok false}` becomes an `ex-info` carrying the daemon's
  `:error` and `:type`, so a remote naming/disjointness refusal surfaces like a local
  one.

  **The bearer token rides on the request the daemon requires it on**: the `conn`
  carries it (`VAELII_API_TOKEN` unless `:token` says otherwise) and every call sets one
  more header on the builder it was already using.  No dependency, no client state, and
  the `conn` is still a map you can read."
  (:refer-clojure :exclude [isa?])
  (:require [clojure.edn :as edn]
            [vaelii.impl.guard :as guard])
  (:import [java.net URI]
           [java.net.http HttpClient HttpClient$Builder
            HttpRequest HttpRequest$Builder HttpRequest$BodyPublishers
            HttpResponse HttpResponse$BodyHandlers]
           [java.time Duration]))

(defn client
  "A connection handle to a daemon at `host`:`port` (opts: `:timeout-ms`, default
  30000).  Holds a reusable `HttpClient`; no network happens until a call.

  `:token` is the bearer token every call presents.  Omitted, it is `VAELII_API_TOKEN`
  (`guard/api-token`) — the same variable the daemon reads, so a client and a daemon in
  one environment agree without either being configured; an explicit nil sends no
  `Authorization` header, which is what an open daemon wants and what a test of the
  refusal needs."
  ([host port] (client host port {}))
  ([host port {:keys [timeout-ms] :or {timeout-ms 30000} :as opts}]
   (let [^HttpClient$Builder b (HttpClient/newBuilder)]
     (.connectTimeout b (Duration/ofMillis timeout-ms))
     {:base-url   (str "http://" host ":" port)
      :timeout-ms timeout-ms
      :token      (if (contains? opts :token) (:token opts) (guard/api-token))
      :http       (.build b)})))

(defn- with-token
  "Set `conn`'s bearer token on the request builder, when it holds one.  One `.header`
  call on the builder each call already makes — the whole of what carrying a credential
  costs this client."
  ^HttpRequest$Builder [^HttpRequest$Builder rb conn]
  (when-let [token (:token conn)]
    (.header rb "authorization" (str "Bearer " token)))
  rb)

(defn- read-reply
  "Parse a daemon reply body, or refuse it typed.

  The daemon answers EDN; anything else on the wire came from something that is not the
  daemon — a proxy's HTML error page, a truncated body — and reading it raised a bare
  `RuntimeException` with no `:type`, or handed back `nil`, which then read as
  `{:ok nil}` and threw \"vaelii daemon: \" with no message and no type.  `Throwable`,
  because a deeply nested reply overflows the reader's stack."
  [^String body]
  (let [form (try (edn/read-string body)
                  (catch Throwable t
                    (throw (ex-info (str "the daemon's reply does not read as EDN: "
                                         (.getMessage t))
                                    {:type :bad-reply :body body}))))]
    (if (map? form)
      form
      (throw (ex-info (str "the daemon's reply is not a map: " (pr-str form))
                      {:type :bad-reply :reply form})))))

(defn- send-edn
  "POST `body` (an EDN string) to `path` and return the parsed EDN reply map.
  `timeout-ms` overrides the `conn`'s, which is what a long `:poll` needs: the daemon
  holds the request open for its wait, and a read timeout shorter than that would fail
  every poll that had nothing to report."
  ([conn path body] (send-edn conn path body (:timeout-ms conn)))
  ([conn path body timeout-ms]
   (let [^HttpClient http (:http conn)
         ^HttpRequest$Builder rb (HttpRequest/newBuilder (URI/create (str (:base-url conn) path)))]
     (.timeout rb (Duration/ofMillis (long timeout-ms)))
     (.header rb "content-type" "application/edn")
     (with-token rb conn)
     (.POST rb (HttpRequest$BodyPublishers/ofString ^String body))
     (let [^HttpResponse resp (.send http (.build rb) (HttpResponse$BodyHandlers/ofString))]
       (read-reply (.body resp))))))

(defn call
  "POST `{:op op :args args}` and return the `:result`, or throw `ex-info` on an
  `{:ok false}` reply.  The low-level entry the convenience fns wrap; use it for an op
  with no wrapper yet.

  `opts` is `{:timeout-ms n}` for this call alone, which only the long `:poll` needs —
  everything else answers inside the `conn`'s own timeout."
  ([conn op args] (call conn op args nil))
  ([conn op args {:keys [timeout-ms]}]
   (let [reply (send-edn conn "/op" (pr-str {:op op :args (vec args)})
                         (or timeout-ms (:timeout-ms conn)))]
     (if (:ok reply)
       (:result reply)
       ;; the daemon's own `:type` when it sent one, so a caller discriminates on the one
       ;; vocabulary `docs/operations.md` promises; `:daemon-error` when it did not, since
       ;; this is the one `ex-info` in the tree that could carry no `:type` at all.
       ;; `or` rather than `merge` defaults: a reply carrying `:type nil` — the key
       ;; present, the value useless — must not defeat the fallback.
       (throw (ex-info (str "vaelii daemon: " (:error reply))
                       (-> (assoc reply :op op :args (vec args))
                           (update :type #(or % :daemon-error)))))))))

(defn health
  "The daemon's liveness reply, `{:ok true}` — a GET, so it needs no op, and the one
  route a daemon answers without the token (`serve/open-routes`).  The header is sent
  when the `conn` holds one all the same: a probe that authenticates where it can is no
  worse off, and this way one code path builds every request."
  [conn]
  (let [^HttpClient http (:http conn)
        ^HttpRequest$Builder rb (HttpRequest/newBuilder (URI/create (str (:base-url conn) "/health")))]
    (with-token rb conn)
    (.GET rb)
    (let [^HttpResponse resp (.send http (.build rb) (HttpResponse$BodyHandlers/ofString))]
      (read-reply (.body resp)))))

;; ---- convenience wrappers: the vaelii.core surface, conn-first ------------
;; Each threads `conn` and forwards the same args the in-process fn takes.  A sentex
;; result comes back as a plain map (the daemon projects the record), a solution as a
;; binding map — the same shapes `vaelii.core` returns.

(defn assert!
  "Assert `sentence` in `context` (optional `opts`) — returns the handle(s)."
  ([conn sentence context] (call conn :assert [sentence context]))
  ([conn sentence context opts] (call conn :assert [sentence context opts])))

(defn assert-rule!
  ([conn antecedents consequent context] (call conn :assert-rule [antecedents consequent context]))
  ([conn antecedents consequent context opts] (call conn :assert-rule [antecedents consequent context opts])))

(defn assert-many
  ([conn sentences context] (call conn :assert-many [sentences context]))
  ([conn sentences context opts] (call conn :assert-many [sentences context opts])))

(defn retract! [conn handle] (call conn :retract [handle]))

(defn sentexes-matching
  ([conn sentence] (call conn :sentexes-matching [sentence]))
  ([conn sentence context] (call conn :sentexes-matching [sentence context])))

(defn query
  ([conn goal] (call conn :query [goal]))
  ([conn goal context] (call conn :query [goal context]))
  ([conn goal context opts] (call conn :query [goal context opts])))

(defn ask
  ([conn goal] (call conn :ask [goal]))
  ([conn goal context] (call conn :ask [goal context])))

(defn ask?
  ([conn goal] (call conn :ask? [goal]))
  ([conn goal context] (call conn :ask? [goal context])))

(defn prove
  ([conn goal] (call conn :prove [goal]))
  ([conn goal context] (call conn :prove [goal context])))

(defn provable?
  ([conn goal] (call conn :provable? [goal]))
  ([conn goal context] (call conn :provable? [goal context])))

(defn in? [conn handle] (call conn :in? [handle]))
(defn believed? [conn handle context] (call conn :believed? [handle context]))
(defn belief-status [conn handle context] (call conn :belief-status [handle context]))
(defn why [conn handle] (call conn :why [handle]))

(defn why-not
  ([conn handle] (call conn :why-not [handle]))
  ([conn sentence context] (call conn :why-not [sentence context])))

(defn isa?
  ([conn x t] (call conn :isa? [x t]))
  ([conn x t context] (call conn :isa? [x t context])))

(defn types-of
  ([conn x] (call conn :types-of [x]))
  ([conn x context] (call conn :types-of [x context])))

(defn genls [conn t] (call conn :genls [t]))
(defn specs [conn t] (call conn :specs [t]))
(defn contexts [conn] (call conn :contexts []))
(defn sentex [conn handle] (call conn :sentex [handle]))
(defn handle-of [conn sentence context] (call conn :handle-of [sentence context]))
(defn find-sentexes [conn term] (call conn :find-sentexes [term]))
(defn conflicts [conn] (call conn :conflicts []))
(defn contradictions [conn] (call conn :contradictions []))
(defn violations [conn] (call conn :violations []))

;; ---- the change feed, held open with a cursor ----------------------------
;; `core/watch` takes a callback and a callback does not cross an EDN wire, so what a
;; remote caller holds is a subscription the daemon keeps and reads forward with a
;; cursor.  Three calls, the same `{:op :args}` envelope as everything above, and no
;; second wire format — docs/feed.md, "Across the wire".

(def ^:private max-wait-ms
  "The longest the daemon parks a long poll, whatever `:wait-ms` asks for.

  Mirrored here rather than required from `vaelii.impl.subscribe`, which would pull the
  whole engine onto the classpath of a client whose whole point is not needing it.  A
  mirrored constant is a constant that drifts, so `client_test` asserts the two agree —
  the coupling is checked rather than assumed."
  30000)

(defn watch
  "Open a change-feed subscription — `{:token t :cursor 0 :max-events n}`.  With no
  goal it is every belief change; with one it is the standing query `core/watch` takes,
  refused identically (`:not-watchable`) when the goal is not answerable from a moved
  region."
  ([conn] (call conn :watch []))
  ([conn goal context] (call conn :watch [goal context])))

(defn poll
  "Read a subscription forward from `cursor` — `{:events [...] :cursor n :lagged k}`.

  `opts` is `{:wait-ms n}`, the long poll: the daemon holds the request open that long
  waiting for the first event.  The read timeout is extended to cover it, which is the
  whole of what a long poll costs this client — no second protocol, no held socket of
  its own, and nothing about the reply changes.

  **`:lagged` is on every reply and is the one field a caller must read**: non-zero, the
  ring dropped that many events before this poll reached them."
  ([conn token cursor] (poll conn token cursor nil))
  ([conn token cursor opts]
   (let [w (:wait-ms opts 0)]
     ;; refused here as well as at the daemon, so a bad value names the option instead of
     ;; reaching `long` as a bare cast error on the way out
     (when-not (nat-int? w)
       (throw (ex-info (str "poll :wait-ms must be a whole number of milliseconds, got "
                            (pr-str w))
                       {:type :unknown-option :options [:wait-ms]})))
     ;; extended by what the daemon will actually wait, not by what was asked for: the
     ;; wait is capped there, so a caller asking for ten minutes would otherwise hold its
     ;; own socket open for ten minutes against a reply that came in thirty seconds
     (call conn :poll (if opts [token cursor opts] [token cursor])
           {:timeout-ms (+ (long (:timeout-ms conn)) (long (min max-wait-ms w)))}))))

(defn unwatch
  "Drop subscription `token`; true if there was one.  Idempotent."
  [conn token] (call conn :unwatch [token]))

(defn watchers
  "What the daemon is holding open — one entry per subscription, with its goal, how many
  events it has been `:delivered`, and how many are still `:pending` on its ring.
  Neither is the *reader's* position, which lives on the client and is a thing the daemon
  has no way to know."
  [conn] (call conn :watchers []))
