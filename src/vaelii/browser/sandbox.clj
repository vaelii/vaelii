;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.sandbox
  "Somewhere safe to be wrong.

  A **sandbox** is a scratch context of one browser session's own, hung below
  `CxWell` so it sees what CxWell sees (every shipped context but the opt-in theories,
  the `kb/middle/` files that state no `genlCx` edge from CxWell) and nothing shipped
  sees it.  A
  reader can therefore use every type, every relation and every rule the KB ships, and
  cannot damage any of them: their content is visible only from inside, and one control
  takes all of it away again.

  Why that shape and not a permission system: visibility here is *logical*, not
  administrative.  `genlCx` already decides what a context can see, and hanging the
  sandbox at the bottom of the context hierarchy gives exactly the asymmetry wanted — everything
  flows in, nothing flows out — with no new concept and nothing to enforce.  A shipped
  rule firing over sandbox facts places its conclusion **in the sandbox**, because
  placement is the maximal common descendant of the rule's context and the antecedents'
  (docs/contexts.md), and the sandbox is the only context below both.  So the derived
  content is inside the thing that gets discarded, without anything arranging for that.

  Four facts about the lifecycle:

  - **The context is created on the first write, not on the first page.**  A reader who
    only looks costs the KB nothing, and a KB full of empty sandboxes would be a KB with
    a `genlCx` edge per idle visitor.
  - **The server mints the session token and tags it.**  The cookie carries the token and
    an HMAC of it under a key fixed at start, and a cookie whose tag does not check is
    replaced with a fresh one, so a client cannot choose a sandbox.  The context name
    carries a digest of the token rather than the token, because every reader sees every
    context's name (`/find`, `CxWell`'s term page, `/op :contexts`).
  - **A process keeps at most `max-sandboxes` per KB.**  Opening one more resets the
    lowest-priority sandbox on the eviction table below (docs/web.md).
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
            [vaelii.browser.access :as v])
  (:import (java.lang.ref WeakReference)
           (java.nio.charset StandardCharsets)
           (java.security MessageDigest SecureRandom)
           (javax.crypto Mac)
           (javax.crypto.spec SecretKeySpec)))

(def cookie-name "vaelii-sandbox")

(def ^:private token-pattern
  "What a session token is: the 32 hex digits `mint-token` makes.  Checked again in
  `context-for` because the token is digested into a **symbol**, and a name built from
  unvalidated input is an injection."
  #"[0-9a-f]{32}")

(def ^:private cookie-pattern
  "A cookie value: the token, a dot, and its 32-hex-digit tag."
  #"([0-9a-f]{32})\.([0-9a-f]{32})")

(defonce ^:private ^SecureRandom rng (SecureRandom.))

(defn- hex
  "The first `n` bytes of `bs` as lowercase hex."
  [bs n]
  (apply str (map #(format "%02x" %) (take n bs))))

(defn mint-token
  "A fresh session token: 128 bits from `SecureRandom`, as 32 hex digits, which need no
  encoding in a cookie or a symbol."
  []
  (let [b (byte-array 16)]
    (.nextBytes rng b)
    (hex b 16)))

(defonce ^:private signing-key
  ;; `VAELII_SANDBOX_KEY`, so a tag checks across restarts and replicas; unset, 32 random
  ;; bytes for this process's life, and every cookie is re-minted after a restart
  (delay (if-let [k (some-> (System/getenv "VAELII_SANDBOX_KEY") str/trim not-empty)]
           (.getBytes ^String k StandardCharsets/UTF_8)
           (let [b (byte-array 32)] (.nextBytes rng b) b))))

(defn- tag
  "The first 128 bits of the HMAC-SHA256 of `token` under the signing key, as hex."
  [^String token]
  (let [mac (Mac/getInstance "HmacSHA256")]
    (.init mac (SecretKeySpec. ^bytes @signing-key "HmacSHA256"))
    (hex (.doFinal mac (.getBytes token StandardCharsets/UTF_8)) 16)))

(defn- verified
  "The token cookie value `v` carries, when its tag is the one the signing key gives it;
  else nil.  The tags compare in constant time."
  [v]
  (when-let [[_ token t] (and v (re-matches cookie-pattern v))]
    (when (MessageDigest/isEqual (.getBytes ^String t StandardCharsets/US_ASCII)
                                 (.getBytes ^String (tag token) StandardCharsets/US_ASCII))
      token)))

(defn context-for
  "The sandbox context named by `token`, or nil when the token is not well-formed.
  `CxSandbox<digest>` satisfies the context naming invariant (`Cx` prefix,
  CapitalCamelCase), so it is an ordinary context in every other respect.  The digest
  is the first 128 bits of the token's SHA-256: the name is listed to every reader, so
  it must not carry the token a cookie holds."
  [token]
  (when (and token (re-matches token-pattern (str token)))
    (let [d (.digest (MessageDigest/getInstance "SHA-256")
                     (.getBytes (str token) StandardCharsets/UTF_8))]
      (symbol (str "CxSandbox" (hex d 16))))))

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
  "This request's session token — the one `wrap-session` put on it, else the cookie's
  when its tag checks, else nil."
  [req]
  (or (::token req) (verified (get (cookies req) cookie-name))))

(defn context-of
  "The sandbox context this request belongs to, or nil when it carries no valid token."
  [req]
  (context-for (token-of req)))

(defn- set-cookie
  "The `Set-Cookie` value for `token`.  A **session** cookie (no `Max-Age`): a sandbox is
  scoped to the sitting.  `HttpOnly` because no script needs it, `SameSite=Lax` so another
  site cannot drive a write with it, and `Secure` when the request came over HTTPS."
  [token secure?]
  (str cookie-name "=" token "." (tag token) "; Path=/; HttpOnly; SameSite=Lax"
       (when secure? "; Secure")))

(defn add-cookie
  "`resp` with one more `Set-Cookie`.  Ring takes a header value as a string or as a
  collection of them, so a second cookie **extends** the header rather than replacing
  what is there.

  Here rather than in `vaelii.browser.web`, which is the other caller: that namespace
  requires this one, so a helper the two share can only live on this side of the edge.
  The case is a response carrying both cookies the browser has — a reader who sets a
  reading preference on the same request that mints their session token — where an
  `assoc` drops whichever of the two ran first."
  [resp c]
  (update-in resp [:headers "Set-Cookie"]
             (fn [prior]
               (cond (nil? prior)    c
                     (string? prior) [prior c]
                     :else           (conj (vec prior) c)))))

;; ---- the eviction table ----------------------------------------------------
;; The sandboxes a KB holds, with each one's activity, so an admission past the cap
;; knows which to reset.  The priority is GreedyDual's aged form: `L` (`:level`) plus
;; `value`, restarted from the current `L` at each use; an eviction raises `L` to the
;; evicted priority.  docs/web.md states the rule and why.

(def max-sentexes
  "How many sentexes one sandbox may store.  `/assert` refuses a form that would take its
  sandbox past this, with `:over-ceiling`; the conclusions an admitted form derives may
  pass it.  Only the lines addressed to the sandbox count: a line the form writes into
  another context counts toward no ceiling."
  2000)

(defn max-sandboxes
  "How many sandboxes a KB holds at most (`VAELII_SANDBOX_MAX`)."
  []
  (v/switch-value "VAELII_SANDBOX_MAX"))

(defn- idle-horizon-ms
  "How long a sandbox may go unused before it is reset ahead of every used one
  (`VAELII_SANDBOX_IDLE_MINUTES`), in milliseconds."
  []
  (* 60000 (v/switch-value "VAELII_SANDBOX_IDLE_MINUTES")))

(defn- now
  "The time the eviction table records, in epoch milliseconds."
  []
  (System/currentTimeMillis))

(def ^:private empty-eviction-table {:level 0.0 :seq 0 :entries {}})

(defn- value
  "What keeping a sandbox is worth: its active minutes past the first, times one plus the
  log of its writes, over one plus the log of its stored sentexes.  A sandbox used inside
  one minute is worth 0, however much it wrote."
  [{:keys [minutes writes size]}]
  (/ (* (dec minutes) (inc (Math/log (max 1 writes))))
     (inc (Math/log (inc size)))))

(defn- note-use
  "`table` with `ctx` used at `t`: its last use and use order set, one more active minute
  when `t` falls in a minute it had none in, and its priority restarted from the level."
  [table ctx t]
  (let [n (inc (:seq table))
        m (quot t 60000)]
    (-> table
        (assoc :seq n)
        (update-in [:entries ctx]
                   (fn [e]
                     (let [e (cond-> (assoc e :last t :seq n)
                               (not= m (:minute e)) (-> (assoc :minute m) (update :minutes inc)))]
                       (assoc e :h (+ (:level table) (value e)))))))))

(defn- enter
  "`table` with `ctx` opened at `t` holding `size` sentexes."
  [table ctx size t]
  (note-use (assoc-in table [:entries ctx] {:minutes 0 :minute -1 :writes 0 :size size}) ctx t))

(defn- used
  "`table` with `ctx` used at `t`, when it is in the table."
  [table ctx t]
  (if (get-in table [:entries ctx]) (note-use table ctx t) table))

(defn- wrote
  "`table` with one more write by `ctx`'s session at `t`, after which it holds `size`."
  [table ctx size t]
  (if (get-in table [:entries ctx])
    (note-use (update-in table [:entries ctx] #(-> % (update :writes inc) (assoc :size size)))
              ctx t)
    table))

(defn- idle? [e t horizon] (> (- t (:last e)) horizon))

(defn- victim
  "The context an admission resets: of those idle past `horizon`, the longest idle; else
  the lowest priority, and of equal priorities the one used least recently."
  [table t horizon]
  (let [rank (fn [[_ e]] (if (idle? e t horizon) [0 (:last e) (:seq e)] [1 (:h e) (:seq e)]))]
    (key (reduce (fn [best kv] (if (neg? (compare (rank kv) (rank best))) kv best))
                 (:entries table)))))

(defn- evict
  "`table` without `ctx`.  The level rises to its priority unless it was idle past
  `horizon`, since an idle sandbox's priority records activity that has stopped."
  [table ctx t horizon]
  (let [e (get-in table [:entries ctx])]
    (cond-> (update table :entries dissoc ctx)
      (and e (not (idle? e t horizon))) (update :level max (:h e)))))

(defn- room
  "`[table' evicted]`: `table` with contexts evicted until fewer than `cap` remain, and
  those contexts in eviction order."
  [table cap t horizon]
  (loop [r table out []]
    (if (< (count (:entries r)) cap)
      [r out]
      (let [c (victim r t horizon)]
        (recur (evict r c t horizon) (conj out c))))))

(defn- edge [ctx] (list 'genlCx ctx 'CxWell))

(defn live?
  "Does this sandbox exist in the KB yet?  It exists exactly when its edge does; the
  extent can be empty (everything in it retracted) and the sandbox still be open."
  [target ctx]
  (boolean (and ctx (v/handle-of target (edge ctx) 'CxUniverse))))

(defn- rebuilt
  "The eviction table for the sandboxes `target` holds, each entered at `t` as a fresh sandbox of
  its size: the activity signals live in this process and a restart loses them."
  [target t]
  (reduce (fn [r ctx] (enter r ctx (v/count-in-context target ctx) t))
          empty-eviction-table
          (sort (filter #(and (str/starts-with? (name %) "CxSandbox") (live? target %))
                        (v/contexts target)))))

;; one `[WeakReference atom]` pair per KB, compared by identity: a KB's hash reads its
;; stores, which change under it
(defonce ^:private eviction-tables (atom []))

(defn- eviction-table-of [target]
  (some (fn [[^WeakReference r a]] (when (identical? target (.get r)) a)) @eviction-tables))

(defn- eviction-table!
  "`target`'s eviction-table atom, built from the KB the first time it is asked for."
  [target]
  (or (eviction-table-of target)
      (locking eviction-tables
        (or (eviction-table-of target)
            (let [a (atom (rebuilt target (now)))]
              (swap! eviction-tables (fn [rs] (conj (filterv (fn [[^WeakReference r]] (.get r)) rs)
                                                    [(WeakReference. target) a])))
              a)))))

(defn note-use!
  "Record a request by the session whose sandbox is `ctx`."
  [target ctx]
  (when-let [a (and ctx (eviction-table-of target))]
    (swap! a used ctx (now))))

(defn note-write!
  "Record a write request by the session whose sandbox is `ctx`, and its size after."
  [target ctx]
  (when-let [a (and ctx (eviction-table-of target))]
    (when (contains? (:entries @a) ctx)
      (swap! a wrote ctx (v/count-in-context target ctx) (now)))))

(defn wrap-session
  "Give every request a session token, minting one into a cookie when the request
  carries none whose tag checks, and record the use against the KB `kb-of` answers.

  The token alone writes nothing — it names a sandbox that may not exist yet.  Only
  `open` creates the context, and only a write calls it."
  [handler kb-of]
  (force signing-key)
  (fn [req]
    (let [known (verified (get (cookies req) cookie-name))
          token (or known (mint-token))
          resp  (handler (assoc req ::token token))]
      (when known (note-use! (kb-of) (context-for known)))
      (cond-> resp
        (nil? known) (add-cookie (set-cookie token (= :https (:scheme req))))))))

;; ---- the context itself --------------------------------------------------

(defn reset!
  "Discard the whole sandbox: every sentex in it, then the edge that made it a context,
  and its eviction-table entry.

  One `edit`, so it is one settle, and the dependency-directed sweep does the rest — a
  conclusion derived into the sandbox goes with the premises it rested on, and its
  justification with it.  Retracting the extent wholesale is safe even though the sweep
  reaches some of it first: a handle already gone is a no-op in `:remove`.

  Answers `{:removed-sentexes n :removed-justifications n}`.  Irreversible, hence the
  `!` — that is the whole point of the control."
  [target ctx]
  (when-let [a (and ctx (eviction-table-of target))]
    (swap! a update :entries dissoc ctx))
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

(defn- make-room!
  "Reset sandboxes until `target` holds fewer than `max-sandboxes`.  An eviction-table entry whose
  sandbox is gone by another path is dropped first."
  [target]
  (let [a   (eviction-table! target)
        cap (max-sandboxes)]
    (when (>= (count (:entries @a)) cap)
      (let [dead (remove #(live? target %) (keys (:entries @a)))
            _    (swap! a update :entries #(apply dissoc % dead))
            [r gone] (room @a cap (now) (idle-horizon-ms))]
        (clojure.core/reset! a r)
        (doseq [c gone] (reset! target c))))))

(defn open
  "Make sure `ctx` exists, and answer it.  Idempotent — the edge is find-or-create, so a
  second call on a live sandbox writes nothing.  Opening a sandbox past `max-sandboxes`
  resets the lowest-priority one first.  Bare, not `!`: it removes only through `reset!`."
  [target ctx]
  (when ctx
    (when-not (live? target ctx)
      (make-room! target)
      (v/edit! target {:add [[(edge ctx) 'CxUniverse {:strength :monotonic}]]})
      (swap! (eviction-table! target) enter ctx 0 (now)))
    ctx))

(defn extent
  "Every sentex stored in the sandbox — what the reader put there and what the shipped
  rules concluded from it, which are in the same place by construction."
  [target ctx]
  (if (and ctx (live? target ctx)) (v/sentexes-in-context target ctx) []))
