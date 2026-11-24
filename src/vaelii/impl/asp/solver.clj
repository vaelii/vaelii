;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.solver
  "Picks the ASP backend per solve: in-process clingo (`vaelii.impl.asp.clingo`, resolved
  on first use so JNA stays optional) or the clasp subprocess.  `asp.edge`, `asp.label` and
  `asp.solve-context` call `solve`, `classify-both` and `available?`.  See docs/asp.md,
  \"Getting a solver\"."
  (:require
   [taoensso.trove :as trove]
   [vaelii.impl.asp.clasp :as clasp]
   [vaelii.impl.config :as config]))

(defn- configured [] (config/asp-solver))

(defn- load-clingo
  "`{:solve :classify-both :available?}` when libclingo loads and answers in this JVM,
  else nil."
  []
  (let [solve (requiring-resolve 'vaelii.impl.asp.clingo/solve)
        cboth (requiring-resolve 'vaelii.impl.asp.clingo/classify-both)
        avail (requiring-resolve 'vaelii.impl.asp.clingo/available?)]
    (when (avail) {:solve solve :classify-both cboth :available? avail})))

;; `load-clingo`'s answer once one is reached, else ::unknown.
(defonce ^:private clingo-verdict (atom ::unknown))

;; Whether a `VirtualMachineError` from `load-clingo` has been logged.
(defonce ^:private clingo-vm-error-logged? (atom false))

(defn- clingo-backend
  "`load-clingo`'s answer, memoized for the process.  A throw memoizes nil, logged at
  `:warn`: a namespace, a class or a native library that failed to load fails the same way
  for the life of the JVM.  A `VirtualMachineError` (out of memory, stack overflow) is a
  state of the JVM and not of the install, so it answers nil for this call only, memoizes
  nothing, and is logged the first time."
  []
  (let [v @clingo-verdict]
    (if (not= ::unknown v)
      v
      (locking clingo-verdict
        (let [v @clingo-verdict]
          (if (not= ::unknown v)
            v
            (try (reset! clingo-verdict (load-clingo))
                 (catch VirtualMachineError e
                   (when (compare-and-set! clingo-vm-error-logged? false true)
                     (trove/log! {:level :warn :id ::clingo-load-vm-error :error e
                                  :msg (str "the in-process clingo backend did not load: "
                                            (ex-message e) "; ASP solves go to clasp until"
                                            " a later call loads it")}))
                   nil)
                 (catch Throwable e
                   (trove/log! {:level :warn :id ::clingo-load-failed :error e
                                :msg (str "the in-process clingo backend did not load: "
                                          (ex-message e) "; ASP solves go to clasp")})
                   (reset! clingo-verdict nil)))))))))

;; The auto-mode size cutoff (docs/asp.md, "Why size picks the backend").  Read per call, so
;; `config/check!` refuses a bad value at `open-kb` rather than at the first solve.
(defn- clingo-max-program-bytes [] (config/clingo-max-program-bytes))

(defn- backend
  "The backend ignoring program size: the configured one, else clingo when it loads,
  else clasp.  `available?` asks it; `backend-for` routes by size."
  []
  (case (configured)
    :clasp  :clasp
    :clingo (if (clingo-backend) :clingo :clasp)   ; fall back if unavailable
    (if (clingo-backend) :clingo :clasp)))

(defonce ^:private clasp-usable
  ;; probed once per JVM: `clasp/available?` forks a process to answer
  (delay (clasp/available?)))

(defn- choose-backend
  "The backend, `:clingo` or `:clasp`, for the `configured` choice (`:clasp`, `:clingo`, or
  nil for auto), whether clingo is `available?`, the program's `nbytes`, the auto-mode
  `max-bytes` cutoff, and whether the clasp binary runs.  A configured `:clingo` falls back
  to clasp when clingo is unavailable.  Auto mode picks clingo when it is available and the
  program is at most `max-bytes`, or when clasp does not run (docs/asp.md, \"Why size picks
  the backend\").  Pure, so the policy is tested without libclingo."
  [configured available? nbytes max-bytes clasp-runs?]
  (case configured
    :clasp  :clasp
    :clingo (if available? :clingo :clasp)
    (if (and available?
             (or (<= (long nbytes) (long max-bytes)) (not clasp-runs?)))
      :clingo
      :clasp)))

(defn- backend-for
  "`choose-backend` for a program of `nbytes`, over the live config, clingo's
  availability and the cutoff."
  [nbytes]
  (choose-backend (configured) (some? (clingo-backend)) nbytes (clingo-max-program-bytes)
                  @clasp-usable))

(defn- solve-on [program mode opts]
  (if (= :clingo (backend-for (count (:aspif program))))
    ((:solve (clingo-backend)) program mode opts)
    (clasp/solve (:aspif program) mode opts)))

(defn solve
  "Solve translated program `{:aspif <text> :stmts <statements>}` in `mode` under solve
  options `opts` (`clasp/solve`'s) on the backend `backend-for` picks by the ASPIF byte
  length, returning the shape `clasp/solve` and `clingo/solve` share.  clingo reads
  `:stmts`, clasp the `:aspif` text."
  ;; neither arity calls the other through the var, so a redef wrapping it sees one call
  ([program mode] (solve-on program mode nil))
  ([program mode opts] (solve-on program mode opts)))

(defn classify-both
  "The cautious and the brave enumeration of `aspif-text`: `{:cautious <result> :brave
  <result>}`, each shaped like `solve`.  clingo loads the program once for both; clasp runs
  two solves."
  [aspif-text]
  (if (= :clingo (backend-for (count aspif-text)))
    ((:classify-both (clingo-backend)) aspif-text)
    {:cautious (clasp/solve aspif-text :classify-true)
     :brave    (clasp/solve aspif-text :classify-supportable)}))

(defn available?
  "True if the selected backend can solve in this environment.  The clasp answer is the
  once-per-JVM probe routing reads."
  []
  (if (= :clingo (backend)) true @clasp-usable))
