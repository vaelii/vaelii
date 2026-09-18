;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.clingo
  "In-process ASP solver: a JNA binding to the native clingo C API (which
   embeds clasp). Same solve modes and return shape as
   `vaelii.impl.asp.clasp/solve`, but without the subprocess + JSON round-trip.

   `solve` takes a translated program map `{:aspif <text> :stmts <statements>}`
   and injects the ground `:stmts` straight through the `clingo_backend_*`
   accessors — no ASPIF text, no temp file, no parse (`backend-load!`). Each
   program atom id is interned as the function symbol `a(<id>)` carrying its s/c
   label; a model's true atoms come back through clingo_model_symbols and are
   mapped to labels through that symbol association, so no show statement is
   emitted. `classify-both` keeps the ASPIF-text path (`clingo_control_load_aspif`
   over a temp file), since one live control serves both enumerations.

   Why in-process: it drops the per-solve fork and JSON round-trip the
   subprocess pays, which is the whole win on the small programs
   `vaelii.impl.asp.solver` routes here.

   The four modes map to clingo configuration passed as command-line arguments
   to clingo_control_new (clingo accepts clasp's flags): --opt-mode=optN so
   brave/cautious enumerate over optimal models only, --enum-mode=brave|cautious,
   --models=0|1. The lexicographic cost vector comes from clingo_model_cost.

   Native lib: a system libclingo (brew install clingo) reachable via
   jna.library.path, or an absolute path in -Dvaelii.clingo.lib. Crash isolation
   is lost vs the subprocess — every native return is checked, every solve handle
   is closed in a finally and every Control is freed in one; a malformed program
   throws rather than segfaults.

   The time limit (`config/asp-time-limit`) is not a flag here — libclingo's
   control takes solver options only and refuses `--time-limit` — so each solve runs
   async and is drained through `clingo_solve_handle_wait` with what remains of the
   budget; a solve still running when it runs out is cancelled and reports the
   interrupted bit, read as `:interrupted`."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.config :as config])
  (:import [com.sun.jna NativeLibrary Function Pointer Memory Native]
           [com.sun.jna.ptr PointerByReference IntByReference LongByReference]))

(def ^:dynamic *clingo-lib*
  "Library name (resolved via jna.library.path) or absolute path to libclingo."
  (or (System/getProperty "vaelii.clingo.lib") "clingo"))

(defonce ^:private lib (delay (NativeLibrary/getInstance ^String *clingo-lib*)))

(defn- func ^Function [nm] (.getFunction ^NativeLibrary @lib nm))

(defn- ci [nm & a] (.invokeInt    (func nm) (object-array a)))

(defn- cv [nm & a] (.invokeVoid   (func nm) (object-array a)))

(defn- cp ^Pointer [nm & a] (.invokePointer (func nm) (object-array a)))

(defn- clingo-error []
  (try (when-let [p (cp "clingo_error_message")] (.getString p 0)) (catch Throwable _ nil)))

(defn- chk! [what r]
  (when (zero? r)
    (throw (ex-info (str "clingo " what " failed: "
                         (or (clingo-error) "libclingo set no error message")
                         " — the library is " (pr-str *clingo-lib*)
                         ", named by the vaelii.clingo.lib system property")
                    {:type :solver-failed :op what})))
  r)

(defn- cstr ^Memory [s]
  (let [b (.getBytes (str s) "UTF-8") m (Memory. (long (inc (alength b))))]
    (.write m 0 b 0 (alength b)) (.setByte m (long (alength b)) (byte 0)) m))

(defn- ptr-array ^Memory [ptrs]
  (let [m (Memory. (long (* Native/POINTER_SIZE (count ptrs))))]
    (doseq [[i p] (map-indexed vector ptrs)] (.setPointer m (long (* i Native/POINTER_SIZE)) p))
    m))

(defn- int-array-mem
  "Pack `ints` as a native int32 array (a `clingo_atom_t*` of unsigned cids, or a
   `clingo_literal_t*` of signed cids). Never zero bytes, so an empty list still
   yields a valid pointer the caller pairs with a count of 0."
  ^Memory [ints]
  (let [m (Memory. (long (* 4 (max 1 (count ints)))))]
    (doseq [[i v] (map-indexed vector ints)] (.setInt m (long (* i 4)) (int v)))
    m))

(defn- wlit-array-mem
  "Pack `[literal weight]` pairs as a `clingo_weighted_literal_t*` — consecutive
   int32 pairs (literal then weight) in native memory."
  ^Memory [wlits]
  (let [m (Memory. (long (* 8 (max 1 (count wlits)))))]
    (doseq [[i [lit w]] (map-indexed vector wlits)]
      (.setInt m (long (* i 8)) (int lit))
      (.setInt m (long (+ (* i 8) 4)) (int w)))
    m))

(def ^:private show-shown   (Integer/valueOf 2))

;; `clingo_show_type_atoms`: every true atom of a model, as its symbol — the view the
;; backend path reads, since a backend-added atom is shown by its symbol association
;; rather than by a #show directive.  `show-shown` (2) reads only atoms a show
;; statement named, which the ASPIF-text classify path emits and this path does not.
(def ^:private show-atoms   (Integer/valueOf 4))

;; `clingo_solve_mode_async | clingo_solve_mode_yield`: models are pulled one at a
;; time, and the search runs on clingo's own thread so a wait on it can time out.
(def ^:private mode-async-yield (Integer/valueOf 3))

(def ^:private result-sat   1)

(def ^:private result-unsat 2)

(def ^:private result-interrupted 8)

(defn- symbol->string [s]
  (let [sz (LongByReference.)]
    (chk! "symbol_to_string_size" (ci "clingo_symbol_to_string_size" (Long/valueOf (long s)) sz))
    (let [n (.getValue sz) buf (Memory. (long n))]
      (chk! "symbol_to_string" (ci "clingo_symbol_to_string" (Long/valueOf (long s)) buf (Long/valueOf (long n))))
      (.getString buf 0))))

(defn- model-symbols
  "The shown symbols of model `m` — the s/c label strings vaelii emits as ASPIF
   type-4 show statements — read back as strings."
  [m]
  (let [sz (LongByReference.)]
    (chk! "model_symbols_size" (ci "clingo_model_symbols_size" m show-shown sz))
    (let [n (.getValue sz)]
      (if (zero? n) []
          (let [buf (Memory. (long (* 8 n)))]
            (chk! "model_symbols" (ci "clingo_model_symbols" m show-shown buf (Long/valueOf n)))
            (mapv symbol->string (.getLongArray buf 0 (int n))))))))

(defn- model-atoms
  "The true atoms of backend model `m`, as label strings, via `sym->label` — the map
   from an interned `a(<id>)` symbol to its show label that `backend-load!` returns.
   Read with `show-atoms` so backend-added atoms come back whatever the show state; a
   returned symbol with no label (none, in practice) is dropped."
  [m sym->label]
  (let [sz (LongByReference.)]
    (chk! "model_symbols_size" (ci "clingo_model_symbols_size" m show-atoms sz))
    (let [n (.getValue sz)]
      (if (zero? n) []
          (let [buf (Memory. (long (* 8 n)))]
            (chk! "model_symbols" (ci "clingo_model_symbols" m show-atoms buf (Long/valueOf n)))
            (into [] (keep sym->label) (.getLongArray buf 0 (int n))))))))

(defn- model-cost [m]
  (let [sz (LongByReference.)]
    (chk! "model_cost_size" (ci "clingo_model_cost_size" m sz))
    (let [n (.getValue sz)]
      (if (zero? n) []
          (let [buf (Memory. (long (* 8 n)))]
            (chk! "model_cost" (ci "clingo_model_cost" m buf (Long/valueOf n)))
            (vec (.getLongArray buf 0 (int n))))))))

(defn- model-optimal? [m]
  (let [buf (Memory. 1)]
    (chk! "model_optimality_proven" (ci "clingo_model_optimality_proven" m buf))
    (not (zero? (.getByte buf 0)))))

(defn- read-model
  "One model as `{:atoms [label ...] :cost [long] :optimal? bool}`.  `read-atoms` reads
   the model's true atoms as label strings — `model-symbols` on the ASPIF-text path,
   a `model-atoms` closure over the symbol→label map on the backend path."
  [m read-atoms]
  {:atoms (read-atoms m) :cost (model-cost m) :optimal? (model-optimal? m)})

(defn- keep-model
  "Fold model `m` into `acc` (`{:models [..] :optimum cost-vec :any-optimal? bool}`)
   under a `retain` policy.  `:optimum` (the lexicographically least cost vector seen)
   and `:any-optimal?` (did any model come back optimality-proven) are tracked here
   rather than derived from `:models` afterwards, so a model `retain` drops still
   counts towards both.

   * `:optimal` — every model whose cost has not since been beaten.  A strictly better
     cost arriving discards what came before, because `finalize` keeps only the models
     at the proven optimum anyway; a search streams improving models, so this is the
     whole stream but the last plateau.
   * `:last` — the newest, and only the newest.  The brave and cautious enumerations
     stream converging approximations and `finalize` reads `(last models)`; every
     earlier one is read for its cost and then discarded."
  [{:keys [models optimum any-optimal?]} m retain]
  (let [c       (:cost m)
        better? (and (seq c) (or (nil? optimum) (neg? (compare (vec c) (vec optimum)))))]
    {:optimum      (if better? c optimum)
     :any-optimal? (or any-optimal? (boolean (:optimal? m)))
     :models       (case retain
                     :last    [m]
                     :optimal (if better? [m] (conj models m)))}))

(defn- drain-models
  "The models solve handle `h` yields that `retain` keeps, in order, read as each
   arrives — `{:models [..] :optimum cost-vec :any-optimal? bool}` (see `keep-model`).

   `limit` is the solve's budget in seconds (`config/asp-time-limit`; 0 is none).
   Each wait for the next model is bounded by what remains of it, and a search still
   running when nothing remains is cancelled — `clingo_solve_handle_get` then carries
   the interrupted bit, and the models read so far ride beside it for diagnostics.

   Retention matters because a search streams: a 400-node colouring at a two-second
   budget yields 618 models to a `:label` solve that reads one, and 184 to a cautious
   enumeration that reads the last.  Every one of them is a map of freshly marshaled
   atom-label strings, and holding all of them costs what none of them are worth.

   `read-atoms` reads each model's true atoms as label strings (see `read-model`)."
  [h limit retain read-atoms]
  (let [deadline (when (pos? limit) (+ (System/nanoTime) (long (* limit 1e9))))
        ready    (Memory. 1)]
    (loop [acc {:models [] :optimum nil :any-optimal? false}]
      (chk! "resume" (ci "clingo_solve_handle_resume" h))
      (let [remaining (if deadline (max 0.0 (/ (- deadline (System/nanoTime)) 1e9)) -1.0)]
        (cv "clingo_solve_handle_wait" h (Double/valueOf (double remaining)) ready)
        (if (zero? (.getByte ready 0))
          (do (chk! "cancel" (ci "clingo_solve_handle_cancel" h)) acc)
          (let [mr (PointerByReference.)]
            (chk! "model" (ci "clingo_solve_handle_model" h mr))
            (if-let [m (.getValue mr)]
              (recur (keep-model acc (read-model m read-atoms) retain))
              acc)))))))

(defn- drain-handle
  "Drain and close the solve handle `hr` holds: `{:result <bitset> :models [...]
   :optimum cost-vec :any-optimal? bool}`, the models being what `retain` kept
   (see `drain-models`).

   The close is in a `finally` — freeing a control with a handle still open is
   undefined behaviour in libclingo, so a native failure inside the drain must not
   skip it — and the close itself is guarded, because a `finally` that throws
   *replaces* the exception on its way out.  The in-flight one is the informative
   one: `chk!` names the native call that failed in `:op`, and that is the only
   record of which one it was.  A close that fails on its own is logged and the
   drain's answer stands; there is nothing left to do about the handle either way.
   The sibling `delete-keep-temps!` guards its own cleanup for the same reason.

   `read-atoms` reads each kept model's true atoms as label strings (see `read-model`)."
  [^PointerByReference hr limit retain read-atoms]
  (let [h (.getValue hr)]
    (try
      (let [drained (drain-models h limit retain read-atoms)
            res     (IntByReference.)]
        (chk! "get" (ci "clingo_solve_handle_get" h res))
        (assoc drained :result (.getValue res)))
      (finally
        (try (ci "clingo_solve_handle_close" h)
             (catch Throwable e
               (trove/log! {:level :warn :id ::close-failed
                            :msg  (str "closing the clingo solve handle failed: " (ex-message e))
                            :data {:op "clingo_solve_handle_close"}})))))))

;; ---- the backend accessors: inject a ground program with no ASPIF text ----

(defn- create-number
  "The clingo number symbol for `n` (`clingo_symbol_create_number`)."
  ^long [n]
  (let [out (LongByReference.)]
    (chk! "symbol_create_number" (ci "clingo_symbol_create_number" (Integer/valueOf (int n)) out))
    (.getValue out)))

(defn- create-function
  "The clingo function symbol `name(args…)` with the given sign
   (`clingo_symbol_create_function`). `args` is a seq of argument symbols."
  ^long [name args positive?]
  (let [n    (count args)
        amem (when (pos? n)
               (let [m (Memory. (long (* 8 n)))]
                 (doseq [[i s] (map-indexed vector args)] (.setLong m (long (* i 8)) (long s)))
                 m))
        out  (LongByReference.)]
    (chk! "symbol_create_function"
          (ci "clingo_symbol_create_function" (cstr name)
              (if amem amem Pointer/NULL) (Long/valueOf (long n))
              (Integer/valueOf (if positive? 1 0)) out))
    (.getValue out)))

(defn- backend-add-atom
  "Intern a fresh program atom carrying symbol `sym` (`clingo_backend_add_atom`),
   returning its `clingo_atom_t` id."
  ^long [backend sym]
  (let [symref (LongByReference. (long sym))
        out    (IntByReference.)]
    (chk! "backend_add_atom" (ci "clingo_backend_add_atom" backend symref out))
    (Integer/toUnsignedLong (.getValue out))))

(defn- backend-rule!
  "Emit a normal (or `choice?`) rule with head atoms `head-cids` and normal body
   `body-lits` (signed cids) through `clingo_backend_rule`. A headless call is an
   integrity constraint; an empty body is unconditional."
  [backend choice? head-cids body-lits]
  (let [hn   (count head-cids)
        bn   (count body-lits)
        hmem (if (pos? hn) (int-array-mem head-cids) Pointer/NULL)
        bmem (if (pos? bn) (int-array-mem body-lits) Pointer/NULL)]
    (chk! "backend_rule"
          (ci "clingo_backend_rule" backend (Integer/valueOf (if choice? 1 0))
              hmem (Long/valueOf (long hn)) bmem (Long/valueOf (long bn))))))

(defn- backend-weight-rule!
  "Emit a weight-body rule — head atoms `head-cids` hold when the satisfied `wlits`
   (signed cids paired with weights) sum to at least `lower` — through
   `clingo_backend_weight_rule`. Headless is a weight integrity constraint."
  [backend choice? head-cids lower wlits]
  (let [hn   (count head-cids)
        wn   (count wlits)
        hmem (if (pos? hn) (int-array-mem head-cids) Pointer/NULL)
        wmem (if (pos? wn) (wlit-array-mem wlits) Pointer/NULL)]
    (chk! "backend_weight_rule"
          (ci "clingo_backend_weight_rule" backend (Integer/valueOf (if choice? 1 0))
              hmem (Long/valueOf (long hn)) (Integer/valueOf (int lower))
              wmem (Long/valueOf (long wn))))))

(defn- backend-minimize!
  "Emit a minimize statement over `wlits` (signed cids paired with weights) at
   `priority` through `clingo_backend_minimize`."
  [backend priority wlits]
  (let [wn   (count wlits)
        wmem (if (pos? wn) (wlit-array-mem wlits) Pointer/NULL)]
    (chk! "backend_minimize"
          (ci "clingo_backend_minimize" backend (Integer/valueOf (int priority))
              wmem (Long/valueOf (long wn))))))

(defn- stmt-vids
  "The vaelii atom ids `stmt` references — the head and show atoms, and the unsigned
   ids of its body/weight literals. The union over a program's statements is the full
   atom universe; the `:show` set alone already covers it."
  [{:keys [type atom head body literals]}]
  (case type
    (:fact :choice :show) [atom]
    :rule              (cons head (map #(Math/abs (long %)) body))
    :constraint        (map #(Math/abs (long %)) body)
    :weight-constraint (map (fn [[l _]] (Math/abs (long l))) literals)
    :weight-rule       (cons head (map (fn [[l _]] (Math/abs (long l))) literals))
    :minimize          (map (fn [[l _]] (Math/abs (long l))) literals)))

(defn- control-backend
  "The backend accessor of live control `ctl` (`clingo_control_backend`) — the handle a
   `clingo_backend_*` batch runs against. Obtained fresh per batch (the accessor is cheap
   and idempotent); each batch brackets its own `begin`/`end`."
  ^Pointer [ctl]
  (let [br (PointerByReference.)]
    (chk! "control_backend" (ci "clingo_control_backend" ctl br))
    (.getValue br)))

(defn- intern-atom!
  "Intern vaelii atom id `vid` on `backend` as the clingo function symbol `a(<vid>)`,
   returning `[cid sym]` — its `clingo_atom_t` and the symbol. Idempotent on one live
   backend: `clingo_backend_add_atom` keys on the (interned) symbol, so a `vid` seen in an
   earlier batch re-interns to the SAME cid. That identity is what lets a later
   incremental batch reference an earlier batch's atoms."
  [backend vid]
  (let [sym (create-function "a" [(create-number vid)] true)]
    [(backend-add-atom backend sym) sym]))

(defn- backend-batch!
  "Run ONE backend batch on the already-obtained `backend`: begin, intern the atom
   universe of `stmts` as `a(<id>)` symbols, emit every head and body/weight literal
   remapped through that vid→cid table (sign preserved on body literals), end. No show
   statement is emitted — the symbol association is the show. Returns
   `{:sym->label <symbol → label> :vid->cid <vid → cid>}`: the map the model readback
   reads through (`model-atoms`, holding only the *labelled* atoms — an unlabelled one is
   dropped there anyway, and omitting it keeps a session's `merge` from clobbering a label
   an earlier batch gave the same atom), and the vid→cid table an incremental session
   accumulates so a later batch — and `assign-external!` — can name these atoms.

   Repeatable on one live control: `clingo_backend_begin`/`_end` bracket a batch and may be
   called again between solves, and clasp retains its learned clauses across them — the
   multi-shot capability `clingo_control_load_aspif` (one-shot) lacks."
  [backend stmts]
  (let [vid->label (into {} (keep (fn [{:keys [type atom text]}]
                                    (when (= :show type) [atom text])))
                         stmts)
        universe   (into (set (keys vid->label)) (mapcat stmt-vids) stmts)]
    (chk! "backend_begin" (ci "clingo_backend_begin" backend))
    (let [entries    (mapv (fn [vid]
                             (let [[cid sym] (intern-atom! backend vid)] [vid cid sym]))
                           (sort universe))
          vid->cid   (into {} (map (fn [[vid cid _]] [vid cid])) entries)
          sym->label (into {} (keep (fn [[vid _ sym]]
                                      (when-let [l (vid->label vid)] [sym l])))
                           entries)
          lit        (fn [l] (if (neg? l) (- (long (vid->cid (- l)))) (long (vid->cid l))))
          wlit       (fn [[l w]] [(lit l) w])]
      (doseq [{:keys [type atom head body bound literals priority]} stmts]
        (case type
          :fact              (backend-rule! backend false [(vid->cid atom)] nil)
          :choice            (backend-rule! backend true  [(vid->cid atom)] nil)
          :rule              (backend-rule! backend false [(vid->cid head)] (map lit body))
          :constraint        (backend-rule! backend false nil (map lit body))
          :weight-constraint (backend-weight-rule! backend false nil bound (map wlit literals))
          :weight-rule       (backend-weight-rule! backend false [(vid->cid head)] bound (map wlit literals))
          :minimize          (backend-minimize! backend priority (map wlit literals))
          :show              nil))
      (chk! "backend_end" (ci "clingo_backend_end" backend))
      {:sym->label sym->label :vid->cid vid->cid})))

(defn- backend-load!
  "Inject the ground program `stmts` into control `ctl` through the `clingo_backend_*`
   accessors — no ASPIF text, no temp file, no parse — as one batch (`backend-batch!` on
   `ctl`'s backend). Returns that batch's `{:sym->label ... :vid->cid ...}`; the one-shot
   `backend-solve` reads only `:sym->label` (the vid→cid table matters to a live session)."
  [ctl stmts]
  (backend-batch! (control-backend ctl) stmts))

(defn- backend-solve
  "Solve the ground program `stmts` in-process through the backend accessors under
   `arg-strs` (clasp-style flags), keeping the models `retain` keeps. Returns the raw
   drain (see `drain-handle`). No temp file: `backend-load!` injects the program and
   hands back the symbol→label map the model readback reads through."
  [arg-strs stmts retain]
  (let [argcs (mapv cstr arg-strs)                       ; retained through control_new
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (long (count argcs)))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    (let [ctl (.getValue ctlr)]
      (try
        (let [{:keys [sym->label]} (backend-load! ctl stmts)
              hr         (PointerByReference.)]
          (chk! "solve" (ci "clingo_control_solve" ctl mode-async-yield Pointer/NULL
                            (Long/valueOf 0) Pointer/NULL Pointer/NULL hr))
          (let [raw (drain-handle hr (config/asp-time-limit) retain
                                  (fn [m] (model-atoms m sym->label)))]
            (when (seq argcs) argcs)                     ; keep arg strings alive past the call
            raw))
        (finally
          (cv "clingo_control_free" ctl))))))

(def ^:private mode-args
  ;; `:label` uses `opt`, not `optN`: `optN` proves the optimum and only THEN yields the
  ;; optimal model(s), so a solve cancelled at the time limit mid-proof has nothing to hand
  ;; back.  `opt` with `--models=0` streams each improving model as the bound descends, and
  ;; `drain`'s `:optimal` retention keeps the lowest-cost one seen — so a completed solve
  ;; ends on the proven optimum (flagged optimal, `finalize` reports `:optimum`) and an
  ;; interrupted one still has its best model in hand (`finalize` reports `:best-effort`).
  ;; `--models=1` would stop at the FIRST, un-optimized model, which is wrong for a labeling.
  ;; `:sat` is that `--models=1`: a program with no objective has nothing to improve, and
  ;; `--models=0` there enumerates every model.
  {:label                ["--opt-mode=opt"  "--models=0"]
   :sat                  ["--models=1"]
   :all-optima           ["--opt-mode=optN" "--models=0"]
   :classify-true        ["--opt-mode=optN" "--enum-mode=cautious" "--models=0"]
   :classify-supportable ["--opt-mode=optN" "--enum-mode=brave"    "--models=0"]})

(def ^:private mode-retention
  "How many of a mode's streamed models `drain-models` has to keep.  `:label` and
   `:all-optima` read the models at the optimum, so every model still on the best
   cost is kept; the two classify modes read `(last models)` alone."
  {:label                :optimal
   :sat                  :last
   :all-optima           :optimal
   :classify-true        :last
   :classify-supportable :last})

(defn- optimal-models [models opt]
  (if (nil? opt) models (filter #(= opt (:cost %)) models)))

(defn- mode-args-or-throw [mode]
  (or (mode-args mode)
      (throw (ex-info (str "unknown clingo mode: " (pr-str mode) " — want one of "
                           (pr-str (vec (sort (keys mode-args)))))
                      {:type :unknown-option :mismatch :bad-value :mode mode :valid (keys mode-args)}))))

(defn- finalize
  "Shared post-processing for the raw drain of either solve path — one-shot
   `backend-solve` or live-control `solve-control` — into the public contract
   (matches vaelii.impl.asp.clasp/solve):
     :status    :optimum | :sat | :best-effort | :unsat | :interrupted | :unknown
     :atoms     vector of label strings
     :cost      optimum cost (nil if no minimize / unsat)
     :witnesses vector of value vectors (only for :all-optima)
     :raw       the drain (diagnostics)

   `:optimum` and `:any-optimal?` come off the drain rather than out of `:models`,
   which holds only what the mode's retention kept (`keep-model`) — a model dropped
   for being off the best cost still had its say in both.

   `:interrupted` is the cancelled search (the time limit ran out) with NO model to
   show for it.  A `:label` search cancelled *after* it had a model in hand is
   `:best-effort` instead: that model satisfies every hard constraint and is the lowest
   cost seen — only its optimality went unproven — so it is an answer worth handing back
   rather than discarding.  A caller that needs a proven optimum reads the status and
   refuses it; one that wants a good labeling under a deadline takes it.  `:all-optima`
   and the classify modes need the search to finish (an incomplete enumeration or a
   cut-short cautious set is unsound), so they stay `:interrupted`."
  [{:keys [result models any-optimal?] opt :optimum :as raw} mode]
  (let [cost  (first opt)
        status (cond
                 (and (pos? (bit-and result result-interrupted))
                      (#{:label :sat} mode) (seq models))   :best-effort
                 (pos? (bit-and result result-interrupted)) :interrupted
                 (pos? (bit-and result result-unsat))       :unsat
                 (and opt any-optimal?)                     :optimum
                 (pos? (bit-and result result-sat))         :sat
                 :else                                       :unknown)]
    (case mode
      (:label :sat)
      {:status status :atoms (vec (:atoms (first (optimal-models models opt)))) :cost cost :raw raw}

      :all-optima
      (let [opts (optimal-models models opt)]
        {:status status :atoms (vec (:atoms (first opts)))
         :cost cost :witnesses (mapv (comp vec :atoms) opts) :raw raw})

      (:classify-true :classify-supportable)
      ;; brave/cautious stream converging approximations; the LAST model is the
      ;; converged consequence set (matches clasp's last-witness semantics).
      {:status status :atoms (vec (:atoms (last models))) :cost cost :raw raw})))

(defn- objective?
  "Do `stmts` hold a minimize statement over at least one literal?  Without one every
   model costs the same, so a search for improving models enumerates them all."
  [stmts]
  (boolean (some #(and (= :minimize (:type %)) (seq (:literals %))) stmts)))

(defn solve
  "Run clingo in-process on translated program `{:aspif <text> :stmts <statements>}` in
   one of the supported modes, injecting `:stmts` through the `clingo_backend_*`
   accessors (no ASPIF text, no temp file, no parse). See `finalize` for the return
   contract.  A `:label` solve of a program with no objective runs as `:sat`: streaming
   improving models there would enumerate every model."
  [{:keys [stmts]} mode]
  (let [mode (if (and (= :label mode) (not (objective? stmts))) :sat mode)]
    (finalize (backend-solve (mode-args-or-throw mode) stmts (mode-retention mode)) mode)))

(defn- load-block!
  "Load the base ASPIF program into `ctl` via clingo_control_load_aspif. NOT
   additive: clingo rejects a second load_aspif (\"incremental aspif programs are
   not supported\"), so this is a one-shot base load for `open-control` — a live
   control solves the program it opened with, and nothing grows it in place.
   Returns the temp File (caller keeps it alive until the control is freed).

   No `deleteOnExit`: its hook set retains one path, unreclaimable, for the
   process's life — the very cost `delete-keep-temps!` exists to keep off a
   long-running daemon. The file is instead deleted here when the write or the
   load throws, since a caller that never receives it has nothing to hand that
   function."
  [ctl aspif-text]
  (let [tmp (java.io.File/createTempFile "vaelii-session" ".aspif")]
    (try
      (spit tmp aspif-text)
      (let [files (ptr-array [(cstr (.getPath tmp))])]
        (chk! "load_aspif" (ci "clingo_control_load_aspif" ctl files (Long/valueOf 1)))
        tmp)
      (catch Throwable e
        (.delete tmp)
        (throw e)))))

(defn open-control
  "Create a live Control with `arg-strs` flags and load the base `aspif-text`.
   Returns `{:ctl Pointer :keep [..]}` — `:keep` holds JNA buffers and temp
   files that must outlive the control (free it with `free-control!`).

   A load that throws frees the control on the way out: the caller is handed an
   exception rather than a handle, so nothing else can free it, and a leaked
   Control is native memory no GC reaches."
  [arg-strs aspif-text]
  (let [argcs (mapv cstr arg-strs)
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (count argcs))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    (let [ctl (.getValue ctlr)]
      (try
        {:ctl ctl :keep [argcs (load-block! ctl aspif-text)]}
        (catch Throwable e
          (cv "clingo_control_free" ctl)
          (throw e))))))

(defn solve-control
  "Solve a live control under `assume-lits` (signed program literals assumed
   for THIS solve only), keeping the models `retain` keeps.  Returns the same drain
   shape as the one-shot path.  The mode flags are fixed at `open-control` time; this
   is the ASPIF-text path (`classify-both` loads via load_aspif), so witnesses come off
   the output table through the `show-shown` view `model-symbols` reads."
  [ctl assume-lits retain]
  (let [amem (int-array-mem assume-lits)
        hr   (PointerByReference.)]
    (chk! "solve" (ci "clingo_control_solve" ctl mode-async-yield
                      (if (seq assume-lits) amem Pointer/NULL)
                      (Long/valueOf (count assume-lits))
                      Pointer/NULL Pointer/NULL hr))
    (let [raw (drain-handle hr (config/asp-time-limit) retain model-symbols)]
      #_{:clj-kondo/ignore [:unused-value]}
      (identity amem)                                   ; keep the buffer alive past the call
      raw)))

(defn free-control!
  "Free a live control and let its keep-alive buffers/temps be reclaimed. Freeing
   twice is a native double free, so a caller frees exactly once — `classify-both`
   does it in a finally."
  [ctl]
  (cv "clingo_control_free" ctl))

(defn delete-keep-temps!
  "Delete every temp File in a control's `:keep` vector — the ASPIF file
   `load-block!`/`open-control` wrote. Call AFTER `free-control!`. Non-File
   keep entries (JNA buffers) are left for GC. Only the `classify-both` path writes a
   temp now (the one-shot `solve` injects its program through the backend accessors and
   writes none); a live control outlives its solve, so `classify-both` calls this
   instead of leaning on deleteOnExit — which in a long-running daemon holds one .aspif
   file, and one never-GC'd JVM DeleteOnExitHook entry, per classify."
  [keep]
  (doseq [k keep :when (instance? java.io.File k)]
    (try (.delete ^java.io.File k) (catch Throwable _ nil))))

;; ---- an incremental session: grow one live control and toggle externals ----
;;
;; `open-control` above base-loads ASPIF text a live control can then only solve, because
;; `clingo_control_load_aspif` is one-shot ("incremental aspif programs are not
;; supported").  The backend accessors are not: `clingo_backend_begin`/`_end` bracket a
;; batch of ground rules and may be called REPEATEDLY on one live `clingo_control`, so a
;; session grows its program in place across `clingo_control_solve` calls and clasp keeps
;; the clauses it learned between them (multi-shot).  Externals
;; (`clingo_backend_external` + `clingo_control_assign_external`) toggle an atom's truth
;; between solves with no re-grounding.  These are backend/multi-shot only — clasp is a
;; one-shot subprocess that cannot toggle them — so they live here, not on the ASPIF text
;; path, and there is no `:external` statement type in `aspif.clj`.

(def ^:private external-type
  "`clingo_external_type_t` — the truth an external atom is declared with on the backend.
   `:release` (3) drops the external entirely; the session API does not expose it."
  {:free 0 :true 1 :false 2 :release 3})

(def ^:private truth-value
  "`clingo_truth_value_t` — the truth `clingo_control_assign_external` forces on an
   external's literal between solves.  Shares 0/1/2 with `external-type`, minus `:release`."
  {:free 0 :true 1 :false 2})

(defn open-session
  "Open an incremental session: a live control created with `arg-strs` flags and NO
   program loaded — the multi-shot analogue of `open-control`, which base-loads ASPIF text
   a live control cannot then grow.  Returns

     {:ctl <Pointer> :syms (atom {}) :cids (atom {}) :keep [argcs]}

   `:syms` accumulates the symbol→label map across every `add-program!` /
   `declare-external!` batch (`solve-session`'s model readback reads through it); `:cids`
   accumulates vid→cid so a later batch and `assign-external!` can name an earlier batch's
   atoms; `:keep` holds the JNA arg buffers that must outlive the control.  Close with
   `close-session!` exactly once (`free-control!`).

   No free-on-throw wrapper, unlike `open-control`: a failed `control_new` throws in
   `chk!` before a control exists, and nothing between the successful create and the
   returned map can throw — a session base-loads nothing."
  [arg-strs]
  (let [argcs (mapv cstr arg-strs)
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (long (count argcs)))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    {:ctl (.getValue ctlr) :syms (atom {}) :cids (atom {}) :keep [argcs]}))

(defn add-program!
  "Grow `session`'s live program by one backend batch of `stmts` — `control_backend` →
   begin → emit → end on the kept control (`backend-batch!`) — merging the batch's
   sym→label into `(:syms session)` and vid→cid into `(:cids session)`.  Because
   `clingo_backend_add_atom` is idempotent on a symbol, a `vid` first seen in an earlier
   batch re-interns to the SAME cid, so a later batch's rules can reference earlier atoms
   and the program genuinely grows in place (clasp keeps its learned clauses across the
   solves between batches).  Returns the session."
  [session stmts]
  (let [{:keys [sym->label vid->cid]} (backend-batch! (control-backend (:ctl session)) stmts)]
    (swap! (:syms session) merge sym->label)
    (swap! (:cids session) merge vid->cid)
    session))

(defn declare-external!
  "Declare atom `vid` an EXTERNAL of `session`'s live control with initial truth `initial`
   (`:free` | `:true` | `:false`), inside a backend `begin`/`end` bracket (it is a backend
   op).  Interns `a(<vid>)` → cid (recording vid→cid, and a sym→label from `label` or
   `(str vid)` so the external is observable in model readback), then
   `clingo_backend_external(backend, cid, <type>)`.  Unlike a rule, an external's truth is
   then toggled between solves by `assign-external!` with NO re-grounding.  Returns the
   session."
  ([session vid initial] (declare-external! session vid initial (str vid)))
  ([session vid initial label]
   (let [backend (control-backend (:ctl session))]
     (chk! "backend_begin" (ci "clingo_backend_begin" backend))
     (let [[cid sym] (intern-atom! backend vid)]
       (chk! "backend_external"
             (ci "clingo_backend_external" backend (Integer/valueOf (int cid))
                 (Integer/valueOf (int (external-type initial)))))
       (chk! "backend_end" (ci "clingo_backend_end" backend))
       (swap! (:cids session) assoc vid cid)
       (swap! (:syms session) assoc sym label)
       session))))

(defn assign-external!
  "Set external `vid`'s truth on `session`'s live control to `truth` (`:free` | `:true` |
   `:false`) via `clingo_control_assign_external`.  A CONTROL op called BETWEEN solves — no
   backend bracket, no open solve handle — that re-grounds nothing, so the next
   `solve-session` sees the flipped value with clasp's learned clauses intact.  The literal
   is the atom's positive program literal, the `clingo_literal_t` cid `declare-external!`
   recorded.  Refuses a `vid` no batch on this session ever interned — there is no literal
   to assign.  Returns the session."
  [session vid truth]
  (let [cid (get @(:cids session) vid)]
    (when (nil? cid)
      (throw (ex-info (str "assign-external!: atom " vid " has no interned cid on this"
                           " session — declare it (declare-external!) or ground a rule over"
                           " it (add-program!) before toggling it")
                      {:type :solver-failed :op "assign_external" :vid vid})))
    (chk! "assign_external"
          (ci "clingo_control_assign_external" (:ctl session)
              (Integer/valueOf (int cid)) (Integer/valueOf (int (truth-value truth)))))
    session))

(defn solve-session
  "Solve `session`'s live control in `mode`, keeping the models the mode reads and reading
   their true atoms back through the session's accumulated sym→label map (`model-atoms`) —
   the backend analogue of `solve-control`, but on the kept control and WITHOUT freeing it,
   so it is callable repeatedly as the program grows and externals toggle.  The clingo
   flags are fixed at `open-session`; `mode` selects only the retention and `finalize`
   post-processing, so it must agree with those flags.  Returns the public `finalize`
   contract (`:status :atoms :cost :raw`)."
  [session mode]
  (let [retain (or (mode-retention mode)
                   (throw (ex-info (str "unknown clingo mode: " (pr-str mode) " — want one of "
                                        (pr-str (vec (sort (keys mode-retention)))))
                                   {:type :unknown-option :mismatch :bad-value :mode mode})))
        syms   @(:syms session)
        hr     (PointerByReference.)]
    (chk! "solve" (ci "clingo_control_solve" (:ctl session) mode-async-yield Pointer/NULL
                      (Long/valueOf 0) Pointer/NULL Pointer/NULL hr))
    (finalize (drain-handle hr (config/asp-time-limit) retain
                            (fn [m] (model-atoms m syms)))
              mode)))

(defn close-session!
  "Free a session's live control (exactly once, like `free-control!`).  Its `:keep` arg
   buffers become reclaimable; a session writes no temp file, so there is nothing else to
   clean up."
  [session]
  (free-control! (:ctl session)))

(defn- config-subkey ^long [conf parent-key name]
  (let [kr (IntByReference.)]
    (chk! "configuration_map_at"
          (ci "clingo_configuration_map_at" conf (Integer/valueOf (int parent-key)) (cstr name) kr))
    (.getValue kr)))

(defn- set-enum-mode!
  "Set clingo's `solve.enum_mode` (\"cautious\" | \"brave\" | \"auto\" | …) on a
   live control, read at the next solve."
  [ctl mode-str]
  (let [cr (PointerByReference.)]
    (chk! "control_configuration" (ci "clingo_control_configuration" ctl cr))
    (let [conf    (.getValue cr)
          root    (let [rr (IntByReference.)]
                    (chk! "configuration_root" (ci "clingo_configuration_root" conf rr))
                    (.getValue rr))
          solve-k (config-subkey conf root "solve")
          enum-k  (config-subkey conf solve-k "enum_mode")]
      (chk! "configuration_value_set"
            (ci "clingo_configuration_value_set" conf (Integer/valueOf (int enum-k)) (cstr mode-str))))))

(defn classify-both
  "Load `aspif-text` ONCE and run both classify enumerations over the one control,
   switching `solve.enum_mode` between them — avoiding the second control_new +
   load_aspif that two separate `solve` calls pay. Returns
   `{:cautious <result> :brave <result>}`, each shaped like `solve` for the
   corresponding classify mode."
  [aspif-text]
  (let [{:keys [ctl keep]} (open-control ["--opt-mode=optN" "--models=0"] aspif-text)]
    (try
      (let [run (fn [enum-mode]
                  (set-enum-mode! ctl enum-mode)
                  ;; both classify modes share finalize's post-processing (last model),
                  ;; and its retention with it
                  (finalize (solve-control ctl [] (mode-retention :classify-true))
                            :classify-true))
            cautious (run "cautious")
            brave    (run "brave")]
        #_{:clj-kondo/ignore [:unused-value]}
        (identity keep)                          ; retain open-control buffers past the solves
        {:cautious cautious :brave brave})
      (finally
        ;; the temps go even when the free throws.  `delete-keep-temps!` is the only
        ;; thing that removes them — there is no `deleteOnExit` to fall back on — so a
        ;; throw out of `free-control!` would leave one .aspif per classify behind in a
        ;; long-running daemon's tmpdir.
        (try (free-control! ctl)
             (finally (delete-keep-temps! keep)))))))

(defn available?
  "True if libclingo can be loaded and called in this JVM."
  []
  (try (cv "clingo_version" (IntByReference.) (IntByReference.) (IntByReference.)) true
       (catch Throwable _ false)))
