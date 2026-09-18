;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.sandbox
  "Somewhere safe to be wrong.

  A **sandbox** is a scratch context of one browser session's own, hung below
  `CxWell` so it sees the whole shipped ontology and nothing shipped sees it.  A
  reader can therefore use every type, every relation and every rule the KB ships, and
  cannot damage any of them: their content is visible only from inside, and one control
  takes all of it away again.

  Why that shape and not a permission system: visibility here is *logical*, not
  administrative.  `genlCx` already decides what a context can see, and hanging the
  sandbox at the bottom of the spindle gives exactly the asymmetry wanted — everything
  flows in, nothing flows out — with no new concept and nothing to enforce.  A shipped
  rule firing over sandbox facts places its conclusion **in the sandbox**, because
  placement is the maximal common descendant of the rule's context and the antecedents'
  (docs/contexts.md), and the sandbox is the only context below both.  So the derived
  content is inside the thing that gets discarded, without anything arranging for that.

  Three facts about the lifecycle:

  - **The context is created on the first write, not on the first page.**  A reader who
    only looks costs the KB nothing, and a KB full of empty sandboxes would be a KB with
    a `genlCx` edge per idle visitor.
  - **The session id is in the context name**, so two readers of one process never share
    one.  It is minted into a cookie by `wrap-session` and validated on the way back in —
    a name is being built from it, and a name built from unvalidated client input is an
    injection.
  - **Reset is a real teardown**, not a flag: every sentex in the extent goes through
    `edit`'s `:remove`, and the `genlCx` edge with them.  The edge is not in the
    extent — `genlCx` is a forced-decontextualized predicate, so it is stored in
    `CxUniverse` — which is why it is fetched by hand rather than swept up with the
    rest.

  Promotion — moving something out of a sandbox into a context that outlives it — is
  deliberately not here.  A sandbox is a dead end, and a dead end that cannot be
  half-escaped is easier to reason about than one with an entry point in it."
  (:refer-clojure :exclude [reset!])
  (:require [clojure.string :as str]
            [vaelii.browser.access :as v]))

(def cookie-name "vaelii-sandbox")

(def ^:private token-pattern
  "What a session token may be.  Hex, because that is what `mint-token` makes, and
  because the token is interpolated into a **symbol** — an unvalidated cookie would let a
  caller name any context it liked, including a shipped one, and write into it."
  #"[0-9a-f]{8,32}")

(defn mint-token
  "A fresh session token: a whole random UUID with the dashes dropped, so hex that
  needs no encoding to sit in either a cookie or a symbol.

  The **whole** UUID rather than half of one.  A token names a sandbox that can be
  read and written, so guessing another session's is guessing its contents; 48 bits
  is thin the moment the browser is reachable by anyone but its operator, and the
  extra 16 characters added no work."
  []
  (str/replace (str (java.util.UUID/randomUUID)) "-" ""))

(defn context-for
  "The sandbox context named by `token`, or nil when the token is not one we minted.
  `CxSandbox<token>` satisfies the context naming invariant (`Cx` prefix,
  CapitalCamelCase), so it is an ordinary context in every other respect."
  [token]
  (when (and token (re-matches token-pattern (str token)))
    (symbol (str "CxSandbox" token))))

(defn- cookies
  "The request's cookies as a map, parsed off the raw header.  Ring's cookie middleware
  would do this too; one header split is cheaper than wrapping every response in a
  codec for the single cookie this browser sets."
  [req]
  (into {}
        (keep (fn [pair]
                (let [[k val*] (str/split (str/trim pair) #"=" 2)]
                  (when (and k val*) [k val*]))))
        (some-> (get-in req [:headers "cookie"]) (str/split #";"))))

(defn token-of
  "This request's session token — the one `wrap-session` put on it, else the cookie's,
  else nil."
  [req]
  (or (::token req) (get (cookies req) cookie-name)))

(defn context-of
  "The sandbox context this request belongs to, or nil when it carries no valid token."
  [req]
  (context-for (token-of req)))

(defn- set-cookie
  "The `Set-Cookie` value for `token`.  A **session** cookie (no `Max-Age`): a sandbox is
  scoped to the sitting, and one that outlived the browser would be a sandbox nobody
  remembers making.  `HttpOnly` because no script needs it, and `SameSite=Lax` so another
  site cannot drive a write with it — the same reasoning as the origin check on every
  POST here."
  [token]
  (str cookie-name "=" token "; Path=/; HttpOnly; SameSite=Lax"))

(defn wrap-session
  "Give every request a session token, minting one into a cookie the first time.

  The token alone writes nothing — it names a sandbox that may not exist yet.  Only
  `open` creates the context, and only a write calls it."
  [handler]
  (fn [req]
    (let [known (get (cookies req) cookie-name)
          valid (when (and known (re-matches token-pattern known)) known)
          token (or valid (mint-token))
          resp  (handler (assoc req ::token token))]
      (cond-> resp
        (nil? valid) (assoc-in [:headers "Set-Cookie"] (set-cookie token))))))

;; ---- the context itself --------------------------------------------------

(defn- edge [ctx] (list 'genlCx ctx 'CxWell))

(defn live?
  "Does this sandbox exist in the KB yet?  It exists exactly when its edge does; the
  extent can be empty (everything in it retracted) and the sandbox still be open."
  [target ctx]
  (boolean (and ctx (v/handle-of target (edge ctx) 'CxUniverse))))

(defn open
  "Make sure `ctx` exists, and answer it.  Idempotent — the edge is find-or-create, so a
  second call on a live sandbox writes nothing.  Bare, not `!`: it only ever adds."
  [target ctx]
  (when ctx
    (when-not (live? target ctx)
      (v/edit! target {:add [[(edge ctx) 'CxUniverse {:strength :monotonic}]]}))
    ctx))

(defn extent
  "Every sentex stored in the sandbox — what the reader put there and what the shipped
  rules concluded from it, which are in the same place by construction."
  [target ctx]
  (if (and ctx (live? target ctx)) (v/sentexes-in-context target ctx) []))

(defn reset!
  "Discard the whole sandbox: every sentex in it, then the edge that made it a context.

  One `edit`, so it is one settle, and the dependency-directed sweep does the rest — a
  conclusion derived into the sandbox goes with the premises it rested on, and its
  justification with it.  Retracting the extent wholesale is safe even though the sweep
  reaches some of it first: a handle already gone is a no-op in `:remove`.

  Answers `{:removed-sentexes n :removed-justifications n}`.  Irreversible, hence the
  `!` — that is the whole point of the control."
  [target ctx]
  (if-not (and ctx (live? target ctx))
    {:removed-sentexes 0 :removed-justifications 0}
    (let [handles (mapv :id (v/sentexes-in-context target ctx))
          gone    (:removed (v/edit! target {:remove handles}))
          ;; the edge last, and separately: `genlCx` is forced-decontextualized, so
          ;; it is stored in CxUniverse and was never in the extent above
          e       (v/handle-of target (edge ctx) 'CxUniverse)
          gone2   (if e (:removed (v/edit! target {:remove [e]}))
                      {:removed-sentexes 0 :removed-justifications 0})]
      (merge-with + gone gone2))))
