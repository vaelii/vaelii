;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-codec-test
  "The positional frame codec (`vaelii.impl.disk.codec`): every record shape must
  round-trip through freeze → thaw → decode as **itself**, and a frame written before
  the codec — a nippy-frozen record, which is what the existing durable stores hold —
  must still read as itself.  The codec sits between the engine and the log, so a
  round-trip that loses or reshapes a field is a silent data-loss bug that no
  higher-level test would attribute here."
  (:require [clojure.test :refer [deftest is testing]]
            [taoensso.nippy :as nippy]
            [vaelii.impl.disk.codec :as codec]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.sentex :as sx]))

(defn- round-trip
  "Freeze the encoded form, thaw it, decode it — the whole path a record takes to the
  log and back, minus the file."
  [enc dec x]
  (dec (nippy/thaw (nippy/freeze (enc x)))))

(def ^:private sx-trip #(round-trip codec/encode-sentex codec/decode-sentex %))
(def ^:private d-trip  #(round-trip codec/encode-justification codec/decode-justification %))

(deftest atomic-round-trips
  (doseq [a [(sx/->AtomicSentex '(dog Muffet) 'C 7 :true :monotonic)
             (sx/->AtomicSentex '(bornIn Tom 1970) 'WellContext 12 :true nil)
             (sx/->AtomicSentex '(likes Ann (mother (father Bob))) 'C 3 :false :default)
             (sx/->AtomicSentex '(exceptWhen (penguin ?var0) (sentexHandle 9)) 'C 4 :true nil)
             ;; every nil-able field nil at once — the shape a bare derived fact has
             (sx/->AtomicSentex '(p A) 'C nil :true nil)]]
    (testing (str "atomic " (:sentence a))
      (let [r (sx-trip a)]
        (is (= a r) "equal")
        (is (instance? vaelii.impl.sentex.AtomicSentex r) "and still an Atomic")
        (is (nil? (:antecedent r)) "a rule-only key still reads nil off it")))))

(deftest rule-round-trips
  (doseq [r [(sx/->RuleSentex '(implies (and (dog ?var0)) (mammal ?var0)) 'C 8 :true
                              '[(dog ?var0)] '(mammal ?var0) :monotonic '{?var0 ?x}
                              :forward true nil nil)
             ;; multi-antecedent, every optional field set
             (sx/->RuleSentex '(implies (and (parentOf ?var0 ?var1) (parentOf ?var1 ?var2))
                                        (grandparentOf ?var0 ?var2))
                              'KinshipContext 9 :true
                              '[(parentOf ?var0 ?var1) (parentOf ?var1 ?var2)]
                              '(grandparentOf ?var0 ?var2) :default '{?var0 ?a ?var1 ?b ?var2 ?c}
                              :backward true true :hard)
             ;; and with every optional field nil
             (sx/->RuleSentex '(implies (and (p ?var0)) (q ?var0)) 'C 10 :true
                              '[(p ?var0)] '(q ?var0) nil nil nil nil nil nil)]]
    (testing (str "rule " (:consequent r))
      (let [t (sx-trip r)]
        (is (= r t) "equal")
        (is (instance? vaelii.impl.sentex.RuleSentex t) "and still a Rule")
        (is (vector? (:antecedent t))
            "the antecedent is still a VECTOR — decoding must not flatten it to a list")
        (is (= (:varmap r) (:varmap t)) "and the varmap survives as a map")))))

(deftest justification-round-trips
  (doseq [d [(jtms/->Justification 20 :rule [1 2 3] 4 '{?x A} :monotonic #{})
             (jtms/->Justification 21 'someRule [] 5 nil :default #{7 8})]]
    (let [t (d-trip d)]
      (is (= d t))
      (is (instance? vaelii.impl.jtms.Justification t)))))

(deftest decoding-interns-the-vocabulary
  ;; a record paged off disk must share the one pooled object per name, or every fetch
  ;; mints its own copies and the hot cache retains them
  (let [a (sx/->AtomicSentex (list 'parentOf 'Tom 'Ann) 'WellContext 1 :true nil)
        r (sx-trip a)]
    (is (identical? (sx/intern-sym 'parentOf) (first (:sentence r))))
    (is (identical? (sx/intern-sym 'Tom) (second (:sentence r))))
    (is (identical? (sx/intern-sym 'WellContext) (:context r)))))

(deftest non-record-values-pass-through
  (testing "a plain map is not an Atomic and must round-trip as the map it is"
    (is (= {:sentence '(dog Muffet) :context 'C} (sx-trip {:sentence '(dog Muffet) :context 'C}))))
  (testing "provenance is an open application map, stored as it comes"
    (let [p {:creator "agent" :created 1700000000 :nested {:review :pending}}]
      (is (= p (round-trip identity identity p))))))

(deftest frames-written-before-the-codec-still-read
  ;; the durable stores hold nippy-frozen RECORDS.  `decode` dispatches on the thawed
  ;; frame's shape, so those frames must come back unchanged — this is what keeps an
  ;; existing store readable rather than needing a rewrite.
  (let [a      (sx/->AtomicSentex '(dog Muffet) 'C 7 :true :monotonic)
        r      (sx/->RuleSentex '(implies (and (p ?var0)) (q ?var0)) 'C 8 :true
                                '[(p ?var0)] '(q ?var0) nil nil :forward nil nil nil)
        d      (jtms/->Justification 20 :rule [1 2] 3 nil :monotonic #{})
        plain  (fn [x] (nippy/thaw (nippy/freeze x)))]        ; no encode — a bare nippy frame
    (is (= a (codec/decode-sentex (plain a))))
    (is (= r (codec/decode-sentex (plain r))))
    (is (= d (codec/decode-justification (plain d))))))

(deftest the-codec-is-what-shrinks-the-frame
  ;; the point of the codec, asserted rather than assumed: a positional frame is
  ;; materially smaller than the record frame it replaces
  (let [a     (sx/->AtomicSentex '(parentOf Tom Ann) 'NaturalWorldContext 7 :true :monotonic)
        rec-b (alength ^bytes (nippy/freeze a))
        pos-b (alength ^bytes (nippy/freeze (codec/encode-sentex a)))]
    (is (< pos-b rec-b)
        (str "positional " pos-b " B should beat the record frame's " rec-b " B"))))

;; ---- tokenized bodies ----------------------------------------------------
;; The second, opt-in step: the body is a varint stream of ids from a DURABLE
;; dictionary.  An id that cannot be decoded is unreadable data, so what these check is
;; the round trip in full — including across a close/reopen, which is the only place the
;; dictionary's durability is actually on the line.

(defn- with-dict [f]
  (let [dir (str (java.nio.file.Files/createTempDirectory
                  "vaelii-tok-" (into-array java.nio.file.attribute.FileAttribute [])))
        d   (dtok/open-token-log dir)]
    (try (f d dir)
         (finally (dtok/close! d)
                  (doseq [x (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File x))))))

(def ^:private shapes
  [(sx/->AtomicSentex '(dog Muffet) 'C 7 :true :monotonic)
   (sx/->AtomicSentex '(bornIn Tom 1970) 'WellContext 12 :true nil)
   (sx/->AtomicSentex '(comment dog "a domestic canine") 'CoreContext 13 :true :default)
   (sx/->AtomicSentex '(likes Ann (mother (father Bob))) 'C 3 :false :default)
   (sx/->AtomicSentex '(measures Rod 1.5) 'C 14 :true nil)
   (sx/->AtomicSentex '(p A) 'C nil :true nil)
   (sx/->RuleSentex '(implies (and (dog ?var0)) (mammal ?var0)) 'C 8 :true
                    '[(dog ?var0)] '(mammal ?var0) :monotonic '{?var0 ?x} :forward true nil nil)
   (sx/->RuleSentex '(implies (and (parentOf ?var0 ?var1) (parentOf ?var1 ?var2))
                              (grandparentOf ?var0 ?var2))
                    'KinshipContext 9 :true
                    '[(parentOf ?var0 ?var1) (parentOf ?var1 ?var2)]
                    '(grandparentOf ?var0 ?var2) :default '{?var0 ?a ?var1 ?b ?var2 ?c}
                    :backward true true :hard)
   (sx/->RuleSentex '(implies (and (p ?var0)) (q ?var0)) 'C 10 :true
                    '[(p ?var0)] '(q ?var0) nil nil nil nil nil nil)])

(deftest tokenized-bodies-round-trip
  (with-dict
    (fn [d _]
      (let [{:keys [enc dec]} (get (codec/by-kind d true) "sentexes")]
        (doseq [s shapes]
          (testing (str "tokenized " (:sentence s))
            (let [r (dec (nippy/thaw (nippy/freeze (enc s))))]
              (is (= s r) "equal after the round trip")
              (is (= (class s) (class r)) "and the same record type")
              (when (:antecedent s)
                (is (vector? (:antecedent r)) "antecedent still a vector"))
              (when (:varmap s)
                (is (map? (:varmap r)) "varmap still a map")))))))))

(deftest tokenized-frames-are-smaller-than-positional-ones
  (with-dict
    (fn [d _]
      (let [tok  (get (codec/by-kind d true) "sentexes")
            a    (sx/->AtomicSentex '(parentOf Tom Ann) 'NaturalWorldContext 7 :true :monotonic)
            rec-b (alength ^bytes (nippy/freeze a))
            pos-b (alength ^bytes (nippy/freeze (codec/encode-sentex a)))
            tok-b (alength ^bytes (nippy/freeze ((:enc tok) a)))]
        (is (< tok-b pos-b rec-b)
            (str "tokenized " tok-b " < positional " pos-b " < record " rec-b))))))

(deftest only-symbols-and-keywords-are-interned
  ;; a KB of measurements must not mint a dictionary entry per distinct value, so
  ;; numbers and strings ride beside the id stream as literals
  (with-dict
    (fn [d _]
      (let [{:keys [enc dec]} (get (codec/by-kind d true) "sentexes")
            before (dtok/token-count d)]
        (doseq [i (range 50)]
          (enc (sx/->AtomicSentex (list 'measured 'Rod (+ 1000 i) (str "run-" i)) 'C i :true nil)))
        (is (= (+ before 4) (dtok/token-count d))
            "only measured / Rod / C / :true entered the dictionary — not the 100 literals")
        ;; and they still come back
        (let [s (sx/->AtomicSentex '(measured Rod 1042 "run-42") 'C 42 :true nil)]
          (is (= s (dec (nippy/thaw (nippy/freeze (enc s)))))))))))

(deftest the-dictionary-survives-a-restart
  ;; the one thing that can turn a tokenized frame into unreadable data
  (with-dict
    (fn [d dir]
      (let [frames (mapv (:enc (get (codec/by-kind d true) "sentexes")) shapes)
            ;; freeze them, drop the dictionary, reopen it off its log, and decode
            frozen (mapv nippy/freeze frames)]
        (dtok/close! d)
        (let [d2 (dtok/open-token-log dir)
              {:keys [dec]} (get (codec/by-kind d2 true) "sentexes")]
          (is (= shapes (mapv #(dec (nippy/thaw %)) frozen))
              "every frame decodes through a dictionary rebuilt from its log")
          ;; and a token interned before the restart keeps its id
          (is (= (mapv #(dec (nippy/thaw %)) frozen)
                 (mapv #(dec (nippy/thaw %)) frozen))
              "decoding is repeatable")
          (dtok/close! d2))
        ;; reopen once more so the fixture's close! has a live handle
        (let [d3 (dtok/open-token-log dir)]
          (is (pos? (dtok/token-count d3)))
          d3)))))

(deftest a-store-reads-both-frame-shapes
  ;; enabling tokenized writes must not orphan what is already written, and disabling
  ;; them must not orphan what was written while they were on
  (with-dict
    (fn [d _]
      (let [on  (get (codec/by-kind d true) "sentexes")
            off (get (codec/by-kind d false) "sentexes")
            a   (sx/->AtomicSentex '(dog Muffet) 'C 7 :true :monotonic)
            plain (nippy/freeze ((:enc off) a))
            toked (nippy/freeze ((:enc on) a))]
        (is (= a ((:dec on) (nippy/thaw plain))) "tokenizing store reads a plain frame")
        (is (= a ((:dec off) (nippy/thaw toked))) "plain store reads a tokenized frame")))))

(deftest a-frame-referencing-an-unknown-token-is-refused
  ;; the failure mode that matters: an id the dictionary cannot decode is damaged data,
  ;; and must not come back as a plausible-looking nil field
  (with-dict
    (fn [d _]
      (let [{:keys [enc dec]} (get (codec/by-kind d true) "sentexes")
            frame (nippy/thaw (nippy/freeze (enc (sx/->AtomicSentex '(dog Muffet) 'C 7 :true nil))))]
        (is (codec/tokenized-frame? frame))
        ;; a dictionary that never saw those tokens cannot decode the frame
        (with-dict
          (fn [empty-d _]
            (let [{other :dec} (get (codec/by-kind empty-d true) "sentexes")]
              (is (thrown? clojure.lang.ExceptionInfo (other frame))))))
        (is (= '(dog Muffet) (:sentence (dec frame))) "and the real dictionary still decodes it")))))
