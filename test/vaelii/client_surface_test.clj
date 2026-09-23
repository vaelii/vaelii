;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.client-surface-test
  "The client's wrapper surface against the daemon's op table — the claim
  `docs/operations.md` makes about it, checked rather than asserted in prose.

  Three things, and they are the three ways the claim could be false: an op with no
  wrapper (a remote caller reaching for `call` and a keyword), a wrapper naming no op (a
  call that 400s at run time on `:unknown-op`), and a wrapper spelling the fn differently
  from `vaelii.core` (a caller who has to remember which side of the wire they are on).

  Plus the drift check that keeps it true: the generated sections are compared against
  what `vaelii.regen-client` would write **now**, so an op added to `serve/ops` reds this
  file until somebody runs `lein regen-client` and reads the diff.  That is the same
  bargain the three goldens make — the red is the notification, not the chore.

  These read var metadata and file text, never a KB, so they are identical across the
  backends and owe the matrix nothing."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.host.client :as client]
            [vaelii.host.serve :as serve]
            [vaelii.regen-client :as regen])
  (:import [java.net URI]
           [java.net.http HttpRequest]))

(def ^:private hand-written
  "The public vars of each client namespace that are **not** op wrappers, so the
  every-wrapper-names-an-op check below has something to except.  Each is here for a
  reason of its own rather than as an exemption:

  - the connection and the escape hatch (`client`, `call`, `health`) — `health` is a GET
    and takes no op at all;
  - the change feed (`watch` / `poll` / `unwatch` / `watchers`), which is
    `serve/feed-ops` rather than a `vaelii.core` fn: `core/watch` takes a callback and a
    callback does not cross an EDN wire (docs/feed.md);
  - `max-wait-ms`, the daemon's own cap mirrored so the client can extend its read
    timeout without requiring the engine;
  - the two deprecated spellings, which name ops that already have a wrapper."
  '{vaelii.host.client #{client call health watch poll unwatch watchers max-wait-ms
                         assert! assert-rule!}
    vaelii.client      #{client call health watch poll unwatch watchers}})

(defn- wrappers
  "The public vars of `ns-sym` that are meant to be op wrappers, by name."
  [ns-sym]
  (require ns-sym)
  (into {} (remove (fn [[nm _]] (contains? (hand-written ns-sym) nm)))
        (ns-publics ns-sym)))

(defn- conn-first-arglists
  "The arglists a wrapper for `op` must carry — `vaelii.core`'s, `kb` replaced by
  `conn` — as a set, since the order a `defn` writes them in is not the claim."
  [op]
  (set (regen/signatures op)))

(deftest every-op-has-a-wrapper-spelled-as-core-spells-the-fn
  (doseq [ns-sym '[vaelii.host.client vaelii.client]]
    (let [ws (wrappers ns-sym)]
      (doseq [op (sort (keys serve/ops))]
        (let [nm (regen/wrapper-name op)]
          (testing (str ns-sym " / " op)
            (is (contains? ws nm)
                (str op " has no wrapper named " nm " — `lein regen-client`"))
            (when-let [v (ws nm)]
              (is (= (conn-first-arglists op) (set (:arglists (meta v))))
                  (str nm " is short of an arity the daemon accepts, which is a read a"
                       " remote caller cannot make")))))))))

(deftest every-wrapper-names-an-op
  ;; The other direction, and the one that catches a rename: a wrapper whose op was
  ;; spelled away is a call that reaches the daemon and comes back `:unknown-op`.
  (let [by-name (into {} (map (juxt regen/wrapper-name identity)) (keys serve/ops))]
    (doseq [ns-sym '[vaelii.host.client vaelii.client]]
      (doseq [nm (sort (keys (wrappers ns-sym)))]
        (is (contains? by-name nm)
            (str ns-sym "/" nm " names no op — either it is an op wrapper whose op went"
                 " away, or it belongs in this test's hand-written roster"))))))

(deftest no-op-resolves-under-both-spellings
  ;; The generator tries the bare `vaelii.core` name and then the `!`-marked one, since
  ;; the daemon's keywords drop the suffix (`:retract` runs `retract!`).  Were both live
  ;; vars for one op, the wrapper would silently be whichever was tried first.
  (doseq [op (sort (keys serve/ops))]
    (let [bare (ns-resolve 'vaelii.core (symbol (name op)))
          bang (ns-resolve 'vaelii.core (symbol (str (name op) "!")))]
      (is (some? (or bare bang)) (str op " resolves to no vaelii.core var"))
      (is (not (and bare bang))
          (str op " resolves to both " (name op) " and " (name op) "!")))))

(deftest the-deprecated-spellings-are-aliases-and-say-so
  ;; Kept because a caller outside this repo may hold them, and dropping a public name is
  ;; Breaking whatever the spelling was worth.  `!` means *irreversible* here, and an
  ;; assertion is not.
  #_{:clj-kondo/ignore [:deprecated-var]}
  (doseq [[o n] [[#'client/assert! #'client/assert]
                 [#'client/assert-rule! #'client/assert-rule]]]
    (let [nm (:name (meta o))]
      (testing (str nm)
        (is (:deprecated (meta o)) (str nm " is kept, so it has to say it is deprecated"))
        (is (re-find #"[Dd]eprecated" (:doc (meta o)))
            "the docstring says so too — metadata is not what a reader sees")
        (is (= (set (:arglists (meta o))) (set (:arglists (meta n))))
            "an alias that is short of an arity is not an alias")))))

(deftest the-generated-sections-are-what-the-generator-would-write
  ;; The drift check.  A red here is an op somebody added to `serve/ops`: run
  ;; `lein regen-client`, read the diff, and commit it with the change that moved it.
  (doseq [{:keys [path] :as target} regen/targets]
    (testing path
      (is (.exists (io/file path)))
      (is (= (slurp (io/file path)) (regen/rendered target))
          (str path " is out of step with vaelii.host.serve/ops — `lein regen-client`")))))

(deftest a-wrapper-body-sends-the-op-it-names
  ;; Read off the file rather than called, because calling one needs a daemon: the
  ;; generated body is `(call conn :op [args…])`, so the op keyword is in the text beside
  ;; the name.  What this catches is a generator that emitted the right name against the
  ;; wrong keyword — which no arity or roster check above can see.
  (let [text (slurp (io/file "src/vaelii/host/client.clj"))]
    (doseq [op (sort (keys serve/ops))]
      (is (re-find (re-pattern (str "\\(defn " (java.util.regex.Pattern/quote
                                                (str (regen/wrapper-name op)))
                                    "\\n(?s).*?\\(call conn "
                                    (java.util.regex.Pattern/quote (str op)) " \\["))
                   text)
          (str (regen/wrapper-name op) " does not send " op)))))

(deftest the-client-requires-no-engine
  ;; The reason the wrappers are generated at build time rather than macroexpanded from
  ;; `serve/ops`: a `require` of the table would put the engine, jetty and reitit on the
  ;; classpath of a namespace whose whole point is not needing them.  A caller extracting
  ;; this one file gets a client, and that is a property with one way to lose it.
  (let [required (->> (ns-refers 'vaelii.host.client)
                      vals
                      (into #{} (map #(ns-name (:ns (meta %))))))
        aliased  (into #{} (map (comp ns-name val)) (ns-aliases 'vaelii.host.client))]
    (is (empty? (filter #{'vaelii.core 'vaelii.host.serve} (into required aliased)))
        "the client reaches the engine only over HTTP")
    (testing "and what it does require is a leaf, so the independence is transitive"
      ;; `guard` and `opts` are `clojure.string` and nothing else; a require of either
      ;; that stopped being a leaf would be an entry point the engine could walk through later,
      ;; without this file changing a line.
      (doseq [ns-sym '[vaelii.host.guard vaelii.impl.opts]]
        (is (every? #(re-find #"^clojure\." (str %))
                    (map (comp ns-name val) (ns-aliases ns-sym)))
            (str ns-sym " requires something beyond clojure.*"))))))

(deftest a-conn-option-the-client-does-not-read-is-refused
  ;; The silent default here is a **credential**: `:tokenn` is not an explicit nil, so
  ;; the conn falls back to `VAELII_API_TOKEN` and a caller meaning to present something
  ;; else — or nothing — presents the environment's token instead.  `:timeout-ms`
  ;; misspelt is the quieter half: 30 s where a long poll was told to wait longer.
  ;; No socket opens; `client` builds a value.
  (doseq [bad [{:timeoutms 500} {:tokenn "x"} {:timeout-ms 500 :retries 3}]]
    (let [e (is (thrown? clojure.lang.ExceptionInfo (client/client "localhost" 4200 bad))
                (pr-str bad))]
      (is (= :unknown-option (:type (ex-data e))) (pr-str bad))
      (is (= [:timeout-ms :token] (:options (ex-data e))) (pr-str bad))))
  (testing "a non-map opts is refused too, rather than reading every key as absent"
    (let [e (is (thrown? clojure.lang.ExceptionInfo (client/client "localhost" 4200 :nope)))]
      (is (= :unknown-option (:type (ex-data e))))))
  (testing "and the two keys it does read still build a conn"
    (let [c (client/client "localhost" 4200 {:timeout-ms 500 :token "t"})]
      (is (= 500 (:timeout-ms c)))
      (is (= "t" (:token c))))))

(deftest a-token-no-http-header-can-carry-is-refused-without-quoting-it
  ;; `guard/api-token` reads VAELII_API_TOKEN **untrimmed** — trimming a secret silently
  ;; changes it — so a value carrying a trailing newline reaches the JDK, which quotes a
  ;; rejected header value *verbatim* in the `IllegalArgumentException` it raises.  That
  ;; message is the credential, in whatever log or reply the exception reaches, which is
  ;; why the throw is replaced rather than left to travel (`vaelii.host.llm.anthropic`
  ;; does the same for its own).  No socket opens: `with-token` sets a header on a
  ;; builder.
  (let [with-token #'client/with-token
        secret     "s3cret-token"
        builder    #(HttpRequest/newBuilder (URI/create "http://127.0.0.1:4200/op"))]
    (doseq [[label bad] [["a trailing newline"  (str secret "\n")]
                         ["an injected header"  (str secret "\r\nX-Injected: 1")]
                         ["a control character" (str secret (char 1))]
                         ["a non-latin-1 char"  (str secret "☃")]]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo (with-token (builder) {:token bad}))
                  label)]
        (is (= :unknown-option (:type (ex-data e))) label)
        (is (not (re-find (re-pattern (java.util.regex.Pattern/quote secret))
                          (str (ex-message e) " " (pr-str (ex-data e)))))
            (str label " — the refusal quotes the token"))))
    (testing "a token a header can carry is set, so the guard refuses only what the JDK does"
      (is (= ["Bearer s3cret-token"]
             (-> ^java.net.http.HttpRequest$Builder (with-token (builder) {:token secret})
                 (.GET) (.build) (.headers) (.allValues "authorization") vec))))
    (testing "and a conn with no token sets no header at all"
      (is (= [] (-> ^java.net.http.HttpRequest$Builder (with-token (builder) {:token nil})
                    (.GET) (.build) (.headers) (.allValues "authorization") vec))))))

;; ---- what comes back off the wire ---------------------------------------

(deftest a-reply-that-is-not-the-daemons-is-refused-with-a-type
  ;; The refusal is for a body that came from something other than the daemon — a
  ;; proxy's HTML error page, a truncated response, an EDN value that is not a reply
  ;; map.  Read bare it surfaces as the reader's own exception, which carries no `:type`
  ;; for a caller to catch on and no body to look at.  No socket opens: the parse is
  ;; handed the string a response would have carried.
  (let [read-reply #'client/read-reply]
    (testing "a body that does not read as EDN at all"
      (let [e (is (thrown? clojure.lang.ExceptionInfo (read-reply "{:ok true" 200)))]
        (is (= :bad-reply (:type (ex-data e))))
        (is (= "{:ok true" (:body (ex-data e)))
            "and it hands the body back, which is the whole of what says who sent it")))
    (testing "and one that reads as EDN and is not a reply"
      (let [e (is (thrown? clojure.lang.ExceptionInfo (read-reply "[:ok true]" 200)))]
        (is (= :bad-reply (:type (ex-data e))))
        (is (= [:ok true] (:reply (ex-data e))))))
    (testing "the status is on the refusal, which is what tells a dead proxy from a
              daemon that answered a truncated body"
      (is (= 502 (:status (ex-data (try (read-reply "<html>502</html>" 502)
                                        (catch clojure.lang.ExceptionInfo e e))))))
      (is (= 200 (:status (ex-data (try (read-reply "<html>502</html>" 200)
                                        (catch clojure.lang.ExceptionInfo e e)))))))
    (testing "a reply the daemon actually sends parses to the map a caller reads"
      (is (= {:ok true :result 3} (read-reply (pr-str {:ok true :result 3}) 200))))))

(deftest a-daemon-refusal-with-no-type-still-leaves-the-caller-one-to-catch
  ;; The client's floor under the promise that every failure carries a `:type`
  ;; (`docs/operations.md`): a reply from an older daemon, or from something standing in
  ;; front of one, may carry none — and an `ex-info` with none is the one refusal a
  ;; caller cannot discriminate on at all.  `send-edn` is pinned, so no socket opens.
  (let [conn     (client/client "localhost" 4200 {:token nil})
        data-of  (fn [reply]
                   (with-redefs [client/send-edn (fn [& _] [400 reply])]
                     (try (client/call conn :contexts []) nil
                          (catch clojure.lang.ExceptionInfo e (ex-data e)))))]
    (testing "a refusal carrying no :type at all"
      (is (= :daemon-error (:type (data-of {:ok false :error "something went wrong"})))))
    (testing "and one carrying the key with nothing in it — present and useless, which a
              merged default would have left in place"
      (is (= :daemon-error (:type (data-of {:ok false :error "x" :type nil})))))
    (testing "a daemon that did send one keeps it, so the fallback is a floor and not a
              flattening"
      (is (= :naming (:type (data-of {:ok false :error "x" :type :naming})))))
    (testing "and the call is on the ex-data either way, since the reply alone does not
              say which op was refused"
      (is (= :contexts (:op (data-of {:ok false :error "x"}))))
      (is (= [] (:args (data-of {:ok false :error "x"})))))
    (testing "and so is the status, which is the coarse client-fault/server-fault split
              under the one :type vocabulary"
      (is (= 400 (:status (data-of {:ok false :error "x" :type :naming})))))
    (testing "an :ok reply is a result rather than a refusal, so the fallback bears on
              failures alone"
      (is (nil? (data-of {:ok true :result ['CxUniverse]}))
          "nothing was thrown, so there is no ex-data to read"))))
