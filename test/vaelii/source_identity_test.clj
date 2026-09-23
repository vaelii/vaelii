;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.source-identity-test
  "The source identity (`vaelii.impl.source-identity`): the digest a reasoning image is
  stamped with.  An edit to prose leaves it unchanged, an edit to a definition recover can
  run changes it, an edit to a definition recover cannot reach leaves it unchanged, two
  reads of one file agree, and the namespace set it reads reaches the namespaces recovery
  runs — including the ones only a quoted symbol names.

  The per-rule tests write a scratch source tree of three namespaces and walk it from
  `vaelii.impl.demo-root/recover`, so each inclusion rule is exercised by one form the rule
  alone covers."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.source-identity :as si]))

(def ^:private ^String base
  "(ns demo.x
     \"The namespace docstring.\"
     (:require [clojure.string :as str]))

   ;; a comment
   (defn f
     \"The docstring.\"
     [x]
     (inc x))

   (defprotocol P
     \"Protocol doc.\"
     (m [this] \"Method doc.\"))

   (def c \"Doc of c.\" 3)")

(deftest prose-edits-leave-the-digest-unchanged
  (let [d (si/forms-digest base)]
    (testing "comments, docstrings, blank lines and (comment …) blocks"
      (is (= d (si/forms-digest
                (str "\n\n;; a new comment\n"
                     (-> base
                         (.replace "The docstring." "A different docstring, longer.")
                         (.replace "The namespace docstring." "Reworded.")
                         (.replace "Protocol doc." "Reworded protocol doc.")
                         (.replace "Method doc." "Reworded method doc.")
                         (.replace "Doc of c." "Reworded doc of c."))
                     "\n(comment (f 1) (f 2))\n")))))
    (testing "a form moved down by inserted lines keeps its digest"
      (is (= d (si/forms-digest (.replace base "(defn f" "\n\n\n(defn f")))))))

(deftest code-and-compiled-metadata-edits-change-the-digest
  (let [d (si/forms-digest base)]
    (is (not= d (si/forms-digest (.replace base "(inc x)" "(dec x)"))) "a body edit")
    (is (not= d (si/forms-digest (.replace base "(def c \"Doc of c.\" 3)" "(def c \"Doc of c.\" 4)")))
        "a def's value")
    (is (not= d (si/forms-digest (.replace base "(def c" "(def ^:dynamic c")))
        "metadata the compiler reads")
    (is (not= d (si/forms-digest (.replace base "[x]" "[^long x]"))) "a type hint")
    (is (not= d (si/forms-digest (.replace base "(def c \"Doc of c.\" 3)" "(def c \"Doc of c.\")")))
        "a def whose only string is its value keeps the string")))

(deftest reader-minted-names-hash-alike-across-reads
  (testing "auto-gensyms and anonymous-fn arguments are renumbered in order of appearance"
    (is (= (si/forms-digest "(defmacro m [x] `(let [y# ~x] (map #(+ % y#) [1 2])))")
           (si/forms-digest "(defmacro m [x] `(let [w# ~x] (map #(+ % w#) [1 2])))"))
        "two spellings of one auto-gensym"))
  (testing "while the order of two minted names still counts"
    (is (not= (si/forms-digest "(defmacro m [] `(let [a# 1 b# 2] [a# b#]))")
              (si/forms-digest "(defmacro m [] `(let [a# 1 b# 2] [b# a#]))")))))

;; ---- the walk over definitions, on a scratch tree ------------------------------

(def ^:private demo
  "The scratch tree: path under the source directory → text.  `recover` is the root; `why`
  and every form marked unreached is outside what it reaches."
  {"vaelii/impl/demo_root.clj"
   "(ns vaelii.impl.demo-root
      (:require [vaelii.impl.demo-lib :as lib]
                [vaelii.impl.demo-proto :as dp]))
    (defn recover [kb]
      (lib/helper kb)
      (dp/label (lib/make kb))
      (lib/area {:shape :square :side kb})
      (lib/with-span (lib/run kb))
      (dp/bag kb))
    (defn why [kb] (lib/unused kb))"

   "vaelii/impl/demo_lib.clj"
   "(ns vaelii.impl.demo-lib
      (:require [clojure.spec.alpha :as s]
                [vaelii.impl.demo-proto :as dp])
      (:import [vaelii.impl.demo_proto Box]))
    (def ^:dynamic *limit* 8)
    (defn helper [kb] (+ kb *limit*))
    (defn unused [kb] (dec kb))
    (defmulti area :shape)
    (defmethod area :square [x] (* (:side x) (:side x)))
    (defmulti shade :tone)
    (defmethod shade :dark [x] (:tone x))
    (defn enter! [] :entered)
    (defmacro with-span [& body] `(do (enter!) ~@body))
    (defn by-name [] :by-name)
    (defn run [kb] ((requiring-resolve 'vaelii.impl.demo-lib/by-name)))
    (defn make [kb] (Box. kb))
    (def registry (atom []))
    (swap! registry conj :first)
    (swap! registry conj :second)
    (s/fdef helper :args (s/cat :kb int?))
    (s/fdef unused :args (s/cat :kb int?))"

   "vaelii/impl/demo_proto.clj"
   "(ns vaelii.impl.demo-proto)
    (defprotocol Labelled (label [x]))
    (defprotocol Unused (ignored [x]))
    (deftype Box [v] Labelled (label [_] v))
    (defrecord Rec [a])
    (deftype Bag [v] Object (toString [_] (str v)))
    (defn bag [v] (str (Bag. v)))
    (extend-type String Labelled (label [s] (count s)))
    (extend-type String Unused (ignored [s] s))"})

(defn- scratch-dir ^java.io.File []
  (let [d (.toFile (java.nio.file.Files/createTempDirectory
                    "source-identity" (make-array java.nio.file.attribute.FileAttribute 0)))]
    (.deleteOnExit d)
    d))

(defn- write-tree!
  "Write `files` (path → text) under a fresh directory, and return the directory."
  ^java.io.File [files]
  (let [d (scratch-dir)]
    (doseq [[p text] files
            :let [f (io/file d p)]]
      (io/make-parents f)
      (spit f text))
    d))

(def ^:private demo-opts
  {:namespace-roots '[vaelii.impl.demo-root]
   :roots           '[vaelii.impl.demo-root/recover]})

(defn- demo-identity
  "The identity of the scratch tree with `edits` applied: each edit `[path from to]`
  replaces the text `from`, which must occur in `path`, with `to`."
  [& edits]
  (let [files (reduce (fn [m [p from to]]
                        (assert (str/includes? (m p) from) (str from " is not in " p))
                        (update m p #(str/replace % from to)))
                      demo edits)]
    (si/source-identity (assoc demo-opts :source-dirs [(str (write-tree! files))]))))

(defn- changes? [& edits]
  (not= (:digest (demo-identity)) (:digest (apply demo-identity edits))))

(def ^:private lib "vaelii/impl/demo_lib.clj")
(def ^:private proto "vaelii/impl/demo_proto.clj")
(def ^:private root "vaelii/impl/demo_root.clj")

(deftest a-reached-definition-changes-the-digest-and-an-unreached-one-does-not
  (is (changes? [lib "(+ kb *limit*)" "(- kb *limit*)"]) "a fn recover calls")
  (is (not (changes? [lib "(dec kb)" "(inc kb)"])) "a fn only `why` calls")
  (is (not (changes? [root "(lib/unused kb)" "(lib/unused (inc kb))"])) "`why` itself")
  (is (not (changes? [lib "(defn unused" "(defn another [] 1)\n(defn unused"]))
      "a new definition nothing calls")
  (is (changes? [root "(defn recover" "(defn- recover"]) "a root made private")
  (testing "the names the digest takes the reached forms under"
    (let [d (si/definitions (assoc demo-opts :source-dirs [(str (write-tree! demo))]))]
      (is (contains? d "vaelii.impl.demo-lib/helper"))
      (is (not (contains? d "vaelii.impl.demo-lib/unused")))
      (is (not (contains? d "vaelii.impl.demo-root/why"))))))

(deftest a-method-of-a-reached-multimethod-is-included
  (is (changes? [lib "(* (:side x) (:side x))" "(+ (:side x) (:side x))"]))
  (is (not (changes? [lib "(:tone x)" "(name (:tone x))"])) "a method of an unreached multimethod")
  (is (changes? [lib "(defmulti shade" "(defmethod area :circle [x] 3)\n(defmulti shade"])
      "a method added to the reached multimethod"))

(deftest an-implementation-of-a-reached-protocol-is-included
  (is (changes? [proto "(label [s] (count s))" "(label [s] (str s))"]) "an extend-type")
  (is (changes? [proto "(label [_] v)" "(label [_] [v])"]) "a deftype's method")
  (is (not (changes? [proto "(ignored [s] s)" "(ignored [s] (str s))"]))
      "an extension of a protocol nothing calls"))

(deftest a-top-level-form-defining-no-var-is-included
  (is (changes? [lib "(swap! registry conj :first)" "(swap! registry conj :third)"])
      "a registration, though nothing reached names `registry`")
  (is (changes? [lib "(swap! registry conj :first)\n    (swap! registry conj :second)"
                 "(swap! registry conj :second)\n    (swap! registry conj :first)"])
      "two registrations reordered"))

(deftest a-reached-macro-and-what-its-syntax-quote-names-are-included
  (is (changes? [lib "`(do (enter!) ~@body)" "`(do (enter!) (enter!) ~@body)"]) "the macro body")
  (is (changes? [lib "(defn enter! [] :entered)" "(defn enter! [] :left)"])
      "a fn only the macro's syntax-quote names"))

(deftest a-reached-def-contributes-its-value-and-metadata
  (is (changes? [lib "(def ^:dynamic *limit* 8)" "(def ^:dynamic *limit* 9)"]) "the value")
  (is (changes? [lib "(def ^:dynamic *limit* 8)" "(def *limit* 8)"]) "`^:dynamic`")
  (is (changes? [lib "(def ^:dynamic *limit* 8)" "(def ^:dynamic ^:const *limit* 8)"]) "`^:const`"))

(deftest a-fully-qualified-quoted-symbol-reaches-its-definition
  (is (changes? [lib "(defn by-name [] :by-name)" "(defn by-name [] :renamed)"])))

(deftest a-deftype-constructed-in-its-own-namespace-is-included
  (is (changes? [proto "(toString [_] (str v))" "(toString [_] (pr-str v))"])
      "a deftype implementing no protocol, named only by its short class name"))

(deftest every-defrecord-is-included
  (is (changes? [proto "(defrecord Rec [a])" "(defrecord Rec [a b])"])
      "a record nothing names, which nippy or the EDN reader can construct by class name"))

(deftest an-fdef-of-a-reached-var-is-included
  (is (changes? [lib "(s/fdef helper :args (s/cat :kb int?))" "(s/fdef helper :args (s/cat :kb any?))"]))
  (is (not (changes? [lib "(s/fdef unused :args (s/cat :kb int?))"
                      "(s/fdef unused :args (s/cat :kb any?))"]))))

(deftest a-root-naming-no-definition-throws
  (is (thrown-with-msg? IllegalStateException #"names no definition"
                        (si/source-identity (assoc demo-opts
                                                   :roots '[vaelii.impl.demo-root/gone]
                                                   :source-dirs [(str (write-tree! demo))])))))

;; ---- the engine ---------------------------------------------------------------

(defn- engine-copy
  "A scratch copy of the engine's `vaelii.core` and `vaelii.impl.*` source, as a
  directory."
  ^java.io.File []
  (let [src (.getParentFile (.getParentFile (io/file (.toURI (io/resource "vaelii/core.clj")))))
        d   (scratch-dir)]
    (doseq [^java.io.File f (cons (io/file src "vaelii/core.clj")
                                  (file-seq (io/file src "vaelii/impl")))
            :when (.isFile f)
            :let [rel (subs (.getPath f) (inc (count (.getPath src))))
                  to  (io/file d rel)]]
      (io/make-parents to)
      (io/copy f to))
    d))

(deftest an-engine-edit-recover-cannot-reach-keeps-the-digest
  (let [d    (engine-copy)
        opts {:source-dirs [(str d)]}
        core (io/file d "vaelii/core.clj")
        text (slurp core)
        was  (:digest (si/source-identity opts))
        edit (fn [from to]
               (assert (str/includes? text from))
               (spit core (str/replace-first text from to))
               (.setLastModified core (- (System/currentTimeMillis) 60000))
               (let [now (:digest (si/source-identity opts))]
                 (spit core text)
                 now))]
    (is (= was (:digest (si/source-identity opts))) "stable across calls")
    (is (= was (edit "(defn why\n" "(defn ^{:edited true} why\n"))
        "`vaelii.core/why`, which no root reaches")
    (is (not= was (edit "(defn open-kb\n" "(defn ^{:edited true} open-kb\n"))
        "`vaelii.core/open-kb`, a root")))

(deftest the-closure-reaches-what-recovery-runs
  (let [c (si/closure)]
    (is (contains? c 'vaelii.impl.recovery))
    (is (contains? c 'vaelii.impl.settle))
    (is (contains? c 'vaelii.core) "reached through wiring's quoted entry points")
    (is (contains? c 'vaelii.impl.dense-jtms)
        "named only by kb's quoted requiring-resolve and by imports")
    (is (not (contains? c 'vaelii.impl.seal))
        "a namespace that requires the reasoning image and that nothing on the path requires")
    (is (every? #(or (= 'vaelii.core %) (.startsWith (str %) "vaelii.impl.")) c)
        "the walk never leaves the engine"))
  (let [d (si/definitions)]
    (is (contains? d "vaelii.impl.settle/settle"))
    (is (contains? d "vaelii.impl.recovery/recover"))
    (is (not (contains? d "vaelii.core/why")))))

(deftest a-namespace-with-only-compiled-code-contributes-its-container
  (testing "clojure.core's __init class loads from the clojure jar"
    (let [a (#'si/compiled-bytes 'clojure.core (volatile! {}))
          b (#'si/compiled-bytes 'clojure.core (volatile! {}))]
      (is (some? a))
      (is (java.util.Arrays/equals ^bytes a ^bytes b))))
  (is (nil? (#'si/compiled-bytes 'vaelii.no-such-namespace (volatile! {})))
      "a namespace with neither source nor compiled code contributes nothing"))

(deftest an-edited-file-is-parsed-again
  (let [f     (java.io.File/createTempFile "source-identity" ".clj")
        u     (.toURL (.toURI f))
        parse #(:bytes (#'si/parse-source u))
        same? #(java.util.Arrays/equals ^bytes %1 ^bytes %2)]
    (try
      (spit f "(ns demo.y) (defn g [x] (inc x))")
      (.setLastModified f (- (System/currentTimeMillis) 60000))
      (let [a (parse)]
        (is (same? a (parse)) "an unchanged file answers the memo entry")
        (testing "an edit that moves the modification time"
          (spit f "(ns demo.y) (defn g [x] (dec x))")
          (is (not (same? a (parse))))))
      (testing "an edit that keeps the length and the modification time, within the window
                after the read before it"
        (spit f "(ns demo.y) (defn g [x] (inc x))")
        (.setLastModified f (- (System/currentTimeMillis) 500))
        (let [b (parse) m (.lastModified f)]
          (spit f "(ns demo.y) (defn g [x] (dec x))")
          (.setLastModified f m)
          (is (not (same? b (parse))))))
      (finally (.delete f)))))

(deftest the-identity-is-stable-and-names-its-libraries
  (let [a (si/source-identity) b (si/source-identity)]
    (is (= a b))
    (is (= (:namespaces a) (count (si/closure))))
    (is (< 1000 (:definitions a)) "the definitions recover and the write entry points reach")
    (is (some #(.startsWith ^String % "nippy-") (:libraries a)) "nippy's jar, with its version")
    (is (some #(.startsWith ^String % "clojure-") (:libraries a)) "clojure's jar")))
