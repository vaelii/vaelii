;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.clingo
  "The in-process ASP backend: a JNA binding to libclingo, with `vaelii.impl.asp.clasp/solve`'s
   modes and return shape.  `solve` injects a translated program's `:stmts` through the
   `clingo_backend_*` accessors (`backend-load!`); `classify-both` loads the ASPIF text once
   over a temp file and runs both enumerations on one control.  The search flags are
   `clasp/search-args`, and the time limit is a cancel at the deadline (`drain-models`).
   Every native return is checked, and every solve handle and control is freed in a
   `finally`.  See docs/asp.md, \"Getting a solver\" and \"The time limit\"."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.asp.clasp :as clasp]
            [vaelii.impl.config :as config])
  (:import [com.sun.jna NativeLibrary Function Pointer Memory Native]
           [com.sun.jna.ptr PointerByReference IntByReference LongByReference]))

(def ^:dynamic *clingo-lib*
  "Library name (resolved via jna.library.path) or absolute path to libclingo.  A blank
  `vaelii.clingo.lib` is unset, as every switch's blank is (`vaelii.impl.config`):
  `-Dvaelii.clingo.lib=` names no library, and read as one it would ask JNA for a
  library called \"\"."
  (or (some-> (System/getProperty "vaelii.clingo.lib") str/trim not-empty) "clingo"))

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

;; `clingo_show_type_atoms`: every true atom of a model, as its symbol — the atom set the
;; backend path reads, since a backend-added atom is shown by its symbol association
;; rather than by a #show directive.  `show-shown` (2) reads only atoms a show
;; statement named, which the ASPIF-text classify path emits and this path does not.
(def ^:private show-atoms   (Integer/valueOf 4))

;; `clingo_solve_mode_async | clingo_solve_mode_yield`: models are pulled one at a
;; time, and the search runs on clingo's own thread so a wait on it can time out.
(def ^:private mode-async-yield (Integer/valueOf 3))

(def ^:private result-sat   1)

(def ^:private result-unsat 2)

(def ^:private result-exhausted 4)

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
  "The true atoms of backend model `m`, as label strings through `sym->label`
   (`backend-load!`'s map), read with `show-atoms`; a symbol with no label is dropped."
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
   under a `retain` policy.  `:optimum` (the least cost vector seen) and `:any-optimal?`
   count every model, kept or not.

   * `:optimal` keeps the models on the best cost seen, dropping them when a better one
     arrives;
   * `:last` keeps only the newest, the one `finalize` reads for the enumerations;
   * `:all` keeps every model, for an enumeration whose models differ in cost."
  [{:keys [models optimum any-optimal?]} m retain]
  (let [c       (:cost m)
        better? (and (seq c) (or (nil? optimum) (neg? (compare (vec c) (vec optimum)))))]
    {:optimum      (if better? c optimum)
     :any-optimal? (or any-optimal? (boolean (:optimal? m)))
     :models       (case retain
                     :last    [m]
                     :all     (conj models m)
                     :optimal (if better? [m] (conj models m)))}))

(defn- drain-models
  "The models solve handle `h` yields that `retain` keeps, in order, read as each
   arrives — `{:models [..] :optimum cost-vec :any-optimal? bool}` (see `keep-model`).

   `limit` is the solve's budget in seconds (`config/asp-time-limit`; 0 is none).  Each
   wait for the next model is bounded by what remains of it, and a search still running
   when nothing remains is cancelled, which sets the interrupted bit.  `read-atoms` reads
   each model's true atoms (`read-model`)."
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

   The close runs in a `finally`, since freeing a control with a handle open is undefined
   in libclingo.  A close that throws is logged and does not replace the exception in
   flight, whose `:op` names the native call that failed."
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

(defn- backend-project!
  "Emit a projection statement over clingo atom ids `cids` through
   `clingo_backend_project`."
  [backend cids]
  (chk! "backend_project"
        (ci "clingo_backend_project" backend (int-array-mem cids) (Long/valueOf (long (count cids))))))

(defn- stmt-vids
  "The vaelii atom ids `stmt` references — the head and show atoms, and the unsigned
   ids of its body/weight literals. The union over a program's statements is the full
   atom universe; the `:show` set alone already covers it."
  [{:keys [type atom atoms head body literals]}]
  (case type
    (:fact :choice :show) [atom]
    :rule              (cons head (map #(Math/abs (long %)) body))
    :constraint        (map #(Math/abs (long %)) body)
    :weight-constraint (map (fn [[l _]] (Math/abs (long l))) literals)
    :weight-rule       (cons head (map (fn [[l _]] (Math/abs (long l))) literals))
    :minimize          (map (fn [[l _]] (Math/abs (long l))) literals)
    :project           atoms))

(defn- control-backend
  "The backend accessor of live control `ctl` (`clingo_control_backend`) — the handle a
   `clingo_backend_*` batch runs against."
  ^Pointer [ctl]
  (let [br (PointerByReference.)]
    (chk! "control_backend" (ci "clingo_control_backend" ctl br))
    (.getValue br)))

(defn- intern-atom!
  "Intern vaelii atom id `vid` on `backend` as the clingo function symbol `a(<vid>)`,
   returning `[cid sym]` — its `clingo_atom_t` and the symbol."
  [backend vid]
  (let [sym (create-function "a" [(create-number vid)] true)]
    [(backend-add-atom backend sym) sym]))

(defn- backend-load!
  "Inject the ground program `stmts` into control `ctl` through the `clingo_backend_*`
   accessors as one batch: intern each atom id as the symbol `a(<id>)`, then emit every
   statement with its literals remapped to clingo atom ids, signs kept.  No show statement
   is emitted.  Returns the map from a labelled atom's symbol to its label, which
   `model-atoms` reads through."
  [ctl stmts]
  (let [vid->label (into {} (keep (fn [{:keys [type atom text]}]
                                    (when (= :show type) [atom text])))
                         stmts)
        universe   (into (set (keys vid->label)) (mapcat stmt-vids) stmts)
        backend    (control-backend ctl)]
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
      (doseq [{:keys [type atom atoms head body bound literals priority]} stmts]
        (case type
          :fact              (backend-rule! backend false [(vid->cid atom)] nil)
          :choice            (backend-rule! backend true  [(vid->cid atom)] nil)
          :rule              (backend-rule! backend false [(vid->cid head)] (map lit body))
          :constraint        (backend-rule! backend false nil (map lit body))
          :weight-constraint (backend-weight-rule! backend false nil bound (map wlit literals))
          :weight-rule       (backend-weight-rule! backend false [(vid->cid head)] bound (map wlit literals))
          :minimize          (backend-minimize! backend priority (map wlit literals))
          :project           (backend-project! backend (map vid->cid atoms))
          :show              nil))
      (chk! "backend_end" (ci "clingo_backend_end" backend))
      sym->label)))

(defn- backend-solve
  "Solve the ground program `stmts` under `arg-strs` (clasp's flags) for at most `limit`
   seconds, keeping the models `retain` keeps.  Returns the raw drain (`drain-handle`)."
  [arg-strs stmts retain limit]
  (let [argcs (mapv cstr arg-strs)                       ; retained through control_new
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (long (count argcs)))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    (let [ctl (.getValue ctlr)]
      (try
        (let [sym->label (backend-load! ctl stmts)
              hr         (PointerByReference.)]
          (chk! "solve" (ci "clingo_control_solve" ctl mode-async-yield Pointer/NULL
                            (Long/valueOf 0) Pointer/NULL Pointer/NULL hr))
          (let [raw (drain-handle hr limit retain (fn [m] (model-atoms m sym->label)))]
            (when (seq argcs) argcs)                     ; keep arg strings alive past the call
            raw))
        (finally
          (cv "clingo_control_free" ctl))))))

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

(defn- mode-args-or-throw [mode opts]
  (or (clasp/mode-flags mode opts)
      (throw (ex-info (str "unknown clingo mode: " (pr-str mode) " — want one of "
                           (pr-str (vec (sort (keys mode-retention)))))
                      {:type :unknown-option :mismatch :bad-value :mode mode :valid (keys mode-retention)}))))

(defn- finalize
  "The raw drain of either solve path (`backend-solve`, `solve-control`) as
   `vaelii.impl.asp.clasp/solve`'s result, `:atoms` holding label strings and `:raw` the
   drain.  A search is stopped short when the interrupted bit is set, or when neither the
   exhausted nor the unsat bit is.  A search holding every model its cap asks for did not
   stop short: one for `:sat`, `opts`' `:models` optimal ones for `:all-optima`.  A stopped
   `:label` or `:sat` search holding a model is `:best-effort`; any other is
   `:interrupted`.  An exhausted search with a cost is `:optimum`, as clasp's `OPTIMUM
   FOUND` is: under `--opt-mode=opt` no streamed model is marked proven."
  [{:keys [result models any-optimal?] opt :optimum :as raw} mode opts]
  (let [cost     (first opt)
        costs    (some-> opt vec)
        optimal? (clasp/optimal-only? opts)
        capped?  (case mode
                   :sat        (boolean (seq models))
                   :all-optima (and (pos-int? (:models opts))
                                    (>= (count (if optimal? (filter :optimal? models) models))
                                        (long (:models opts))))
                   false)
        stopped? (or (pos? (bit-and result result-interrupted))
                     (and (zero? (bit-and result (bit-or result-exhausted result-unsat)))
                          (not capped?)))
        status   (cond
                   (and stopped? (#{:label :sat} mode) (seq models)) :best-effort
                   stopped?                                          :interrupted
                   (pos? (bit-and result result-unsat))              :unsat
                   (and opt (or any-optimal?
                                (pos? (bit-and result result-exhausted)))) :optimum
                   (pos? (bit-and result result-sat))                :sat
                   :else                                             :unknown)]
    (case mode
      (:label :sat)
      {:status status :atoms (vec (:atoms (first (optimal-models models opt)))) :cost cost :costs costs
       :raw raw}

      :all-optima
      (let [ms (if optimal? (optimal-models models opt) models)]
        {:status status :atoms (vec (:atoms (first ms))) :cost cost :costs costs
         :witnesses (mapv (comp vec :atoms) ms) :witness-costs (mapv #(not-empty (vec (:cost %))) ms)
         :raw raw})

      (:classify-true :classify-supportable)
      ;; the last model is the converged consequence set
      {:status status :atoms (vec (:atoms (last models))) :cost cost :costs costs :raw raw})))

(defn- objective?
  "Do `stmts` hold a minimize statement over at least one literal?  Without one every
   model costs the same, so a search for improving models enumerates them all."
  [stmts]
  (boolean (some #(and (= :minimize (:type %)) (seq (:literals %))) stmts)))

(defn solve
  "Run clingo in-process on translated program `{:aspif <text> :stmts <statements>}` in
   one of `clasp/solve`'s modes under its solve options `opts`, injecting `:stmts` through the `clingo_backend_*`
   accessors (no ASPIF text, no temp file, no parse). See `finalize` for the return
   contract.  A `:label` solve runs as `:sat` as `clasp/solve`'s does: streaming
   improving models there would enumerate every model."
  ([program mode] (solve program mode nil))
  ([{:keys [stmts]} mode opts]
   (let [mode (if (and (= :label mode) (not (and (objective? stmts) (clasp/optimal-only? opts))))
                :sat
                mode)]
     (clasp/without-optimum
      (finalize (backend-solve (into (mode-args-or-throw mode opts) (clasp/search-args opts)) stmts
                               (if (and (= :all-optima mode) (not (clasp/optimal-only? opts)))
                                 :all
                                 (mode-retention mode))
                               (clasp/solve-seconds opts))
                mode opts)
      opts))))

(defn- load-block!
  "Load `aspif-text` into `ctl` through `clingo_control_load_aspif`, once: clingo refuses
   a second load.  Returns the temp File, which the caller deletes after freeing the
   control (`delete-keep-temps!`).  A write or load that throws deletes the file here.
   No `deleteOnExit`, whose hook holds one path per call for the life of the process."
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
  "Create a live Control with `arg-strs` flags and load `aspif-text`.  Returns `{:ctl
   Pointer :keep [..]}`, `:keep` holding the JNA buffers and temp file that must outlive
   the control (`free-control!`).  A load that throws frees the control first."
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
  "Solve a live control under `assume-lits` (signed literals assumed for this solve only),
   keeping the models `retain` keeps; the drain shape of `backend-solve`.  The control was
   loaded from ASPIF text, so witnesses are read through the show statements
   (`model-symbols`)."
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
  "Free a live control, exactly once: a second free is a native double free."
  [ctl]
  (cv "clingo_control_free" ctl))

(defn delete-keep-temps!
  "Delete every temp File in a control's `:keep` vector, after `free-control!`.  JNA
   buffers are left for the GC."
  [keep]
  (doseq [k keep :when (instance? java.io.File k)]
    (try (.delete ^java.io.File k) (catch Throwable _ nil))))

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
  "Load `aspif-text` once and run the cautious and the brave enumeration on one control,
   switching `solve.enum_mode` between them.  Returns `{:cautious <result> :brave
   <result>}`, each shaped like `solve`'s."
  [aspif-text]
  (let [{:keys [ctl keep]} (open-control (into ["--opt-mode=optN" "--models=0"] (clasp/search-args))
                                         aspif-text)]
    (try
      (let [run (fn [enum-mode]
                  (set-enum-mode! ctl enum-mode)
                  (finalize (solve-control ctl [] (mode-retention :classify-true))
                            :classify-true nil))
            cautious (run "cautious")
            brave    (run "brave")]
        #_{:clj-kondo/ignore [:unused-value]}
        (identity keep)                          ; retain open-control buffers past the solves
        {:cautious cautious :brave brave})
      (finally
        ;; the temps go even when the free throws: nothing else deletes them
        (try (free-control! ctl)
             (finally (delete-keep-temps! keep)))))))

(defn available?
  "True if libclingo can be loaded and called in this JVM."
  []
  (try (cv "clingo_version" (IntByReference.) (IntByReference.) (IntByReference.)) true
       (catch Throwable _ false)))
