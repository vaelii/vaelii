;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.codec
  "How a record is shaped on its way into a log frame, and back.

  nippy freezes a Clojure record by writing its **type tag and every field name** into
  the frame — so a store of 100M sentexes writes `vaelii.impl.sentex.LiteralSentex` and
  `:sentence :context :id :truth :strength` 100M times.  Measured on the real corpus,
  that scaffolding is **56% of the store** (87 of 155 B/record) and it says nothing a
  frame needs to carry: the field layout is a property of the code, identical in every
  frame.

  So a frame holds the fields **positionally** — a plain vector, the shape known here —
  which is 1.85× smaller and needs no dictionary, no id allocation, and no new durable
  ground truth (`lein bench-records`).  The codec is per *kind*, because each kind has
  one known set of shapes: a sentex frame is tagged `literal`/`rule`, a justification frame
  is a bare vector (there is only one shape), and provenance is an open application map
  that passes through untouched.

  **Reading is backward-compatible in both directions.**  `decode` dispatches on the
  thawed frame: a vector is positional, anything else is returned as it thawed.  So a
  store written before this codec reads exactly as it did (its frames are records), and
  a plain map handed to `put-sentex` — which the tests do, and which is not a `LiteralSentex`
  — round-trips as the map it is.

  Decoding also **interns** the symbols it rebuilds (`sentex/intern-deep`), so a record
  paged off disk shares the one vocabulary object per name with every other record and
  with the in-memory store, rather than minting its own copy per fetch.  That matters
  most for the records the hot cache retains.

  **Tokenized bodies** are the second, opt-in step (`vaelii.disk.tokens`): the positional
  frame still spells its sentence out in full, and the vocabulary — the same few hundred
  thousand predicate and individual names — is written into every one of the frames.  A
  tokenized frame replaces the s-expression fields with a varint byte string of ids from
  the durable dictionary (`vaelii.impl.disk.tokens`), 2.6× smaller again.  It is a
  *fourth and fifth frame tag*, not a format change: a store can hold plain and tokenized
  frames side by side, so enabling it costs no rewrite and disabling it leaves what is
  already written readable."
  (:require [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.sentex :as sx])
  (:import [java.io ByteArrayOutputStream]))

(def ^:private literal-tag 0)
(def ^:private rule-tag   1)
(def ^:private literal-tok-tag 2)
(def ^:private rule-tok-tag   3)

;; ---- sentexes -----------------------------------------------------------

(defn encode-sentex
  "An `LiteralSentex` or `RuleSentex` as a positional vector; anything else unchanged."
  [sx]
  (condp instance? sx
    vaelii.impl.sentex.LiteralSentex
    [literal-tag (:sentence sx) (:context sx) (:id sx) (:truth sx) (:strength sx)]

    vaelii.impl.sentex.RuleSentex
    [rule-tag (:sentence sx) (:context sx) (:id sx) (:truth sx) (:antecedent sx)
     (:consequent sx) (:strength sx) (:varmap sx) (:direction sx) (:defeasible sx)
     (:assumption sx) (:constraint sx)]

    sx))

(defn decode-sentex
  "The inverse of `encode-sentex`: a positional vector back to its record (symbols
  interned), anything else as it thawed."
  [v]
  (if-not (vector? v)
    v
    (let [f (fn [i] (sx/intern-deep (nth v i)))
          tag (nth v 0)]
      (cond
        (= rule-tag tag)
        (sx/->RuleSentex (f 1) (f 2) (nth v 3) (nth v 4) (f 5) (f 6) (nth v 7) (f 8)
                         (nth v 9) (nth v 10) (nth v 11) (nth v 12))
        (= literal-tag tag)
        (sx/->LiteralSentex (f 1) (f 2) (nth v 3) (nth v 4) (nth v 5))
        ;; a tag this build does not read is a frame from some other build — refused
        ;; by name, never misread as a literal record whose fields land in the wrong
        ;; slots (the tokenized tags decode on their own path, dictionary in hand)
        :else
        (throw (ex-info (str "unknown sentex frame tag " (pr-str tag) " — this path reads"
                             " tag " literal-tag " (literal) and " rule-tag " (rule), and"
                             " the two tokenized twins decode with the dictionary in"
                             " hand; a tag outside those four is a frame some other build"
                             " wrote")
                        {:type :unknown-frame :tag tag}))))))

;; ---- justifications ---------------------------------------------------------
;; One shape, so the frame needs no tag.

(defn encode-justification
  "A `Justification` as a positional vector; anything else unchanged."
  [d]
  (if (instance? vaelii.impl.jtms.Justification d)
    [(:id d) (:informant d) (:antecedents d) (:consequence d) (:bindings d)
     (:strength d) (:out d)]
    d))

(defn decode-justification [v]
  (if-not (vector? v)
    v
    (jtms/->Justification (nth v 0) (sx/intern-deep (nth v 1)) (nth v 2) (nth v 3)
                          (sx/intern-deep (nth v 4)) (nth v 5) (nth v 6))))

;; ---- tokenized bodies ---------------------------------------------------
;; A body is walked in prefix order into one int stream: an interned symbol/keyword is
;; its dictionary id (>= 0), structure and the non-interned atoms are negative control
;; codes.  The stream is then zigzag-varint'd into a byte string, so an id costs one or
;; two bytes where a name costs its length.
;;
;; Numbers and strings are NOT interned — a KB of measurements would mint a dictionary
;; entry per distinct value — so they ride in a side vector of literals that the stream
;; references by position.  Most facts carry none, and nippy freezes the empty vector in
;; two bytes.

(def ^:private LIST-OPEN  -1)
(def ^:private LIST-CLOSE -2)
(def ^:private VEC-OPEN   -3)
(def ^:private VEC-CLOSE  -4)
(def ^:private MAP-OPEN   -5)
(def ^:private MAP-CLOSE  -6)
(def ^:private LIT        -7)          ; followed by the literal's index
(def ^:private NIL        -8)
(def ^:private TRUE       -9)
(def ^:private FALSE     -10)

(defn- write-varint! [^ByteArrayOutputStream out ^long v]
  (loop [z (bit-xor (bit-shift-left v 1) (bit-shift-right v 63))]   ; zigzag
    (if (zero? (bit-and z (bit-not 0x7f)))
      (.write out (int z))
      (do (.write out (int (bit-or (bit-and z 0x7f) 0x80)))
          (recur (unsigned-bit-shift-right z 7))))))

(defn- emit!
  "Append `x` to the id stream, interning its symbols/keywords and parking any other
  atom in `lits`."
  [^ByteArrayOutputStream out dict lits x]
  (letfn [(w [v] (write-varint! out (long v)))]
    (cond
      (nil? x)                      (w NIL)
      (true? x)                     (w TRUE)
      (false? x)                    (w FALSE)
      (or (symbol? x) (keyword? x)) (w (dtok/intern! dict x))
      (vector? x)                   (do (w VEC-OPEN)
                                        (doseq [e x] (emit! out dict lits e))
                                        (w VEC-CLOSE))
      (map? x)                      (do (w MAP-OPEN)
                                        (doseq [[k v] x]
                                          (emit! out dict lits k)
                                          (emit! out dict lits v))
                                        (w MAP-CLOSE))
      (sequential? x)               (do (w LIST-OPEN)
                                        (doseq [e x] (emit! out dict lits e))
                                        (w LIST-CLOSE))
      :else                         (do (w LIT) (w (count @lits)) (vswap! lits conj x)))))

(defn- encode-body
  "`[bytes literals]` for the whole field list — **one** id stream and one literal
  vector for every s-expression field of a record, so the frame pays nippy's per-value
  overhead once rather than once per field."
  [dict xs]
  (let [out  (ByteArrayOutputStream. 48)
        lits (volatile! [])]
    (doseq [x xs] (emit! out dict lits x))
    [(.toByteArray out) @lits]))

;; The reader walks a ByteBuffer, whose own position is the cursor — a body is decoded
;; on every fetch, so it allocates only what it rebuilds.

(defn- read-varint! ^long [^java.nio.ByteBuffer bb]
  (loop [shift 0, acc 0]
    (let [b   (long (.get bb))
          acc (bit-or acc (bit-shift-left (bit-and b 0x7f) shift))]
      (if (zero? (bit-and b 0x80))
        (bit-xor (unsigned-bit-shift-right acc 1) (- (bit-and acc 1)))   ; un-zigzag
        (recur (+ shift 7) acc)))))

(defn- form-from
  "Rebuild one form from control code `v` and whatever follows it in `bb`.  The code is
  passed in rather than read here, because a container's loop must read the next code to
  discover whether it is the close marker and cannot then push it back.  A non-negative
  code is a dictionary id, which `dtok/token` refuses rather than decodes if the
  dictionary does not hold it."
  [^java.nio.ByteBuffer bb dict lits ^long v]
  (cond
    (not (neg? v))    (dtok/token dict v)
    (== v NIL)        nil
    (== v TRUE)       true
    (== v FALSE)      false
    (== v LIT)        (nth lits (read-varint! bb))
    (== v LIST-OPEN)  (loop [acc (transient [])]
                        (let [n (read-varint! bb)]
                          (if (== n LIST-CLOSE)
                            (apply list (persistent! acc))
                            (recur (conj! acc (form-from bb dict lits n))))))
    (== v VEC-OPEN)   (loop [acc (transient [])]
                        (let [n (read-varint! bb)]
                          (if (== n VEC-CLOSE)
                            (persistent! acc)
                            (recur (conj! acc (form-from bb dict lits n))))))
    (== v MAP-OPEN)   (loop [acc (transient {})]
                        (let [n (read-varint! bb)]
                          (if (== n MAP-CLOSE)
                            (persistent! acc)
                            (let [k (form-from bb dict lits n)]
                              (recur (assoc! acc k (form-from bb dict lits (read-varint! bb))))))))
    :else             (throw (ex-info (str "malformed tokenized record body — the code is "
                                           v ", and a body holds a non-negative"
                                           " dictionary id or one of this codec's"
                                           " sentinels")
                                      {:type :malformed-record :code v}))))

(defn- body-reader
  "A thunk yielding the encoded fields back in order."
  [dict ^bytes bs lits]
  (let [bb (java.nio.ByteBuffer/wrap bs)]
    (fn [] (form-from bb dict lits (read-varint! bb)))))

;; The field order each tag's body carries.  Everything that is a symbol, keyword,
;; boolean or nil rides *in* the stream (interned, so `:true` and `:monotonic` cost an
;; id apiece rather than their names); only the handle stays positional, since it is
;; unique per record and interning it is exactly what a dictionary must never do.

(defn- encode-sentex-tok [dict sx]
  (condp instance? sx
    vaelii.impl.sentex.LiteralSentex
    (let [[bs lits] (encode-body dict [(:sentence sx) (:context sx) (:truth sx) (:strength sx)])]
      [literal-tok-tag bs lits (:id sx)])

    vaelii.impl.sentex.RuleSentex
    (let [[bs lits] (encode-body dict [(:sentence sx) (:context sx) (:truth sx)
                                       (:antecedent sx) (:consequent sx) (:strength sx)
                                       (:varmap sx) (:direction sx) (:defeasible sx)
                                       (:assumption sx) (:constraint sx)])]
      [rule-tok-tag bs lits (:id sx)])

    (encode-sentex sx)))

(defn- decode-sentex-tok [dict v]
  ;; read the fields into named locals in the order they were written — `let` makes the
  ;; correspondence with the encoder checkable, where positional constructor arguments
  ;; would leave it resting on evaluation order
  (let [rd (body-reader dict (nth v 1) (nth v 2))
        id (nth v 3)]
    (if (== (long (nth v 0)) (long rule-tok-tag))
      (let [sentence (rd) context (rd) truth (rd) antecedent (rd) consequent (rd)
            strength (rd) varmap (rd) direction (rd) defeasible (rd)
            assumption (rd) constraint (rd)]
        (sx/->RuleSentex sentence context id truth antecedent consequent strength varmap
                         direction defeasible assumption constraint))
      (let [sentence (rd) context (rd) truth (rd) strength (rd)]
        (sx/->LiteralSentex sentence context id truth strength)))))

;; ---- the per-kind table -------------------------------------------------

(defn- sentex-codec [dict tokenize?]
  {:enc (if (and tokenize? dict) #(encode-sentex-tok dict %) encode-sentex)
   ;; reading is never conditional: the frame's own tag says which shape it is, so a
   ;; store holding plain, tokenized and pre-codec frames at once reads all three
   :dec (fn [v]
          (if (and (vector? v) (#{literal-tok-tag rule-tok-tag} (nth v 0)))
            (decode-sentex-tok dict v)
            (decode-sentex v)))})

(defn tokenized-frame?
  "Whether a thawed frame spells its body as dictionary ids — what a store must have a
  dictionary to read."
  [v]
  (boolean (and (vector? v) (#{literal-tok-tag rule-tok-tag} (nth v 0)))))

(defn by-kind
  "`kind-name -> {:enc :dec}` for a store.  `dict` is its durable token dictionary, which
  a store that has ever written a tokenized frame needs **whether or not it still writes
  them** — `tokenize?` governs only the encoder.  Provenance is an open application map
  with no fixed shape, so it is stored as it comes."
  [dict tokenize?]
  {"sentexes"   (sentex-codec dict tokenize?)
   "justifications" {:enc encode-justification :dec decode-justification}
   "provenance" {:enc identity         :dec identity}})
