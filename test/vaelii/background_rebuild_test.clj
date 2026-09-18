;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.background-rebuild-test
  "`:recover? :background` over a `:disk-snapshot` store whose reasoning image was written
  under other engine source.  The open installs the image, and the KB answers from it and
  refuses writes.  Belief is rebuilt under this build on a second KB over the same stores,
  and one `vreset!` then replaces the installed belief with the rebuilt one; a read view
  taken before it reads the installed belief whole.  A close or a `recover` during the
  rebuild stops the rebuild first."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.util.concurrent CountDownLatch TimeUnit]
           [vaelii.impl.types.kb KB]
           [vaelii.impl.types.reasoning Reasoning]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-rebuild-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- manifest ^File [dir] (io/file dir "reasoning" "manifest.edn"))

(defn- stamp [dir] (edn/read-string (slurp (manifest dir))))

(defn- restamp! [dir k v] (spit (manifest dir) (pr-str (assoc (stamp dir) k v))))

(defn- store!
  "A closed `:disk-snapshot` store holding a taxonomy edge and a membership, whose image
  is stamped as written under the engine source \"stale\"."
  ^String []
  (let [dir (tmpdir)
        kb  (v/open-kb {:backend :disk-snapshot :dir dir})]
    (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(dog Rex) 'CxUniverse)
    (v/close! kb)
    (restamp! dir :source "stale")
    dir))

(defn- dogs [kb] (mapv v/sentence-of (v/sentexes-matching kb '(dog ?x) 'CxUniverse)))

(defn- open-held
  "Open `dir` under `:recover? :background` with the rebuild held before its install until
  `release` counts down or the rebuild is asked to stop.  Returns `[kb reached release]`;
  `reached` counts down when the rebuild arrives at the hold."
  [dir]
  (let [reached (CountDownLatch. 1)
        release (CountDownLatch. 1)
        kb      (binding [recovery/*before-install*
                          (fn [_]
                            (.countDown reached)
                            (loop [i 0]
                              (when (and (pos? (.getCount release))
                                         (not (recovery/abandoning?))
                                         (< i 6000))
                                (Thread/sleep 5)
                                (recur (inc i)))))]
                  (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background}))]
    [kb reached release]))

(defn- await-rebuilt
  "Wait up to 30 s for `kb`'s rebuilt belief to be installed; true when it was."
  [kb]
  (loop [i 0]
    (cond
      (empty? (kb/write-hazards kb)) true
      (< i 3000)                     (do (Thread/sleep 10) (recur (inc i)))
      :else                          false)))

(deftest every-kb-field-is-shared-owned-or-the-belief-a-rebuild-makes-new
  (let [dir (store!)
        kb  (v/open-kb {:backend :disk-snapshot :dir dir})]
    (try
      (let [shared (set kb/rebuild-shared)
            own    (set kb/rebuild-own)
            fields (into (set (map keyword (KB/getBasis))) (keys kb))]
        (is (= fields (conj (set/union shared own) :reasoning))
            "a KB field other than `:reasoning` must be named in `kb/rebuild-shared` or `kb/rebuild-own`")
        (is (empty? (set/intersection shared own)))
        (is (not-any? #{:reasoning} (set/union shared own)))
        (is (= (set (map keyword (Reasoning/getBasis))) (set (keys (reasoning/of kb))))
            "`kb/empty-reasoning` makes exactly the `Reasoning` fields")
        (is (not-any? nil? (vals (reasoning/of kb))) "and fills every one")
        (let [r (kb/rebuild-kb kb)]
          (doseq [f shared]
            (is (identical? (get kb f) (get r f)) (str f " is shared with the rebuild KB")))
          (doseq [f own]
            (is (or (nil? (get r f)) (not (identical? (get kb f) (get r f))))
                (str f " is not shared with the rebuild KB")))
          (doseq [[f x] (reasoning/of r)]
            (is (not (identical? x (get (reasoning/of kb) f)))
                (str f " is the rebuild KB's own")))))
      (finally (v/close! kb) (rm-rf! dir)))))

(deftest no-source-reads-a-belief-field-off-the-kb-by-keyword
  ;; The KB record has no `Reasoning` field, so a keyword read of one off a KB answers nil and
  ;; fails nowhere at compile time.  The readers in `vaelii.impl.types.reasoning` are the way
  ;; in, and this scans the tree for the keyword read.
  (let [re   (re-pattern (str "\\(:(" (str/join "|" (map name (Reasoning/getBasis)))
                              ") (kb|kb#|kb1|kb2|ref-kb)\\)"))
        hits (for [dir      ["src" "test" "bench"]
                   ^File f  (file-seq (io/file dir))
                   :when    (str/ends-with? (.getName f) ".clj")
                   [i line] (map-indexed vector (str/split-lines (slurp f)))
                   :when    (re-find re line)]
               (str (.getPath f) ":" (inc i)))]
    (is (empty? hits) "read a `Reasoning` field through `vaelii.impl.types.reasoning`")))

(def ^:private unviewed
  "The public fns taking a KB first that are neither writes nor reads run against
  `kb/read-view`.  `close!` stops the rebuild and releases the KB's own directory.
  `with-deferred-settle` is a macro.  The rest read or set subscriptions, caches,
  statistics or hazards rather than belief, or open another KB."
  #{#'v/close! #'v/with-deferred-settle #'v/watch #'v/unwatch #'v/watchers #'v/caches
    #'v/clear-caches #'v/reset-settle-stats! #'v/write-hazards #'v/fork #'v/load-foreign!})

(deftest every-public-fn-taking-a-kb-is-a-write-a-viewed-read-or-unviewed
  (let [takes-kb? (fn [v] (let [as (:arglists (meta v))]
                            (and (seq as) (every? #(= 'kb (first %)) as))))
        kb-fns    (set (filter takes-kb? (vals (ns-publics 'vaelii.core))))
        writes    (set (keys @#'v/write-ops))
        reads     (set (map #(ns-resolve 'vaelii.core (symbol (name %))) @#'v/read-ops))]
    (is (= kb-fns (set/union writes reads unviewed))
        "a public fn taking a KB first must be in `write-ops`, `read-ops` or `unviewed`")
    (is (empty? (set/intersection writes reads)))
    (is (empty? (set/intersection writes unviewed)))
    (is (empty? (set/intersection reads unviewed)))
    (is (not-any? #(:macro (meta %)) reads) "a macro cannot be wrapped as a read")))

(deftest a-read-view-taken-before-the-install-reads-the-installed-belief-whole
  ;; The install is one `vreset!`, so the read it has to get right is one that takes the
  ;; network before the install and the taxonomy after it.  The view here is taken before
  ;; the install and read after it.
  (let [dir (store!)
        [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
    (try
      (is (.await reached 30 TimeUnit/SECONDS) "the rebuild reaches its install")
      (let [rex     (v/handle-of kb '(dog Rex) 'CxUniverse)
            ;; each half of a reading shows which belief it came from
            reading (fn [k] [(jtms/in? (reasoning/tms k) rex)
                             (contains? (set (tax/genls-global (reasoning/taxonomy k) 'dog)) 'ghost)])]
        ;; move the installed belief away from what the records say, in the network and in
        ;; the taxonomy, so the rebuilt belief differs from it in both
        (jtms/suspend-premise (reasoning/tms kb) rex)
        (tax/add-genl (reasoning/taxonomy kb) 'dog 'ghost 999999)
        (is (= [false true] (reading kb)))
        (let [view (kb/read-view kb)]
          (is (not (identical? kb view)) "while the install is pending, a view is a copy")
          (.countDown release)
          (is (await-rebuilt kb) "the rebuilt belief is installed within 30 s")
          (is (= [true false] (reading kb)) "the KB reads the rebuilt belief")
          (is (= [false true] (reading view)) "the view reads the installed belief, both halves")
          (is (identical? kb (kb/read-view kb)) "with no install pending, the view is the KB")
          (is (= ['(dog Rex)] (dogs kb)) "and a public read reads the rebuilt belief")))
      (finally
        (.countDown release)
        (v/close! kb)
        (rm-rf! dir)))))

(deftest a-stale-image-answers-while-belief-is-rebuilt-behind-it
  (let [dir (store!)
        [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
    (try
      (is (.await reached 30 TimeUnit/SECONDS) "the rebuild reaches its install")
      (testing "the installed image answers, and writes are refused"
        (is (= ['(dog Rex)] (dogs kb)))
        (is (= {:stale-belief true} (kb/write-hazards kb)))
        (let [e (try (v/assert kb '(dog Fido) 'CxUniverse) nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (= :unrecovered-kb (:type (ex-data e))))
          (is (= [:stale-belief] (:hazards (ex-data e)))))
        (is (thrown? clojure.lang.ExceptionInfo
                     (binding [v/*write-unrecovered?* true]
                       (v/assert kb '(dog Fido) 'CxUniverse)))
            "*write-unrecovered?* does not open a KB whose belief is being rebuilt")
        (is (= "stale" (:source (stamp dir))) "the image is not rewritten before the install"))
      ;; move the installed belief away from what the records say, so the install shows
      (jtms/suspend-premise (reasoning/tms kb) (v/handle-of kb '(dog Rex) 'CxUniverse))
      (is (= [] (dogs kb)))
      (.countDown release)
      (is (await-rebuilt kb) "the rebuilt belief is installed within 30 s")
      (testing "the rebuilt belief replaces the installed belief, and writes are accepted"
        (is (= ['(dog Rex)] (dogs kb)))
        (is (not= "stale" (:source (stamp dir))) "the rebuild writes an image under this build")
        (is (some? (v/assert kb '(dog Fido) 'CxUniverse))))
      (finally
        (.countDown release)
        (v/close! kb)
        (rm-rf! dir)))))

(deftest a-close-during-the-rebuild-stops-it-and-the-next-open-recovers
  (let [dir (store!)
        [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
    (try
      (is (.await reached 30 TimeUnit/SECONDS))
      (v/close! kb)
      (is (= "stale" (:source (stamp dir))) "a stopped rebuild installs nothing and writes no image")
      (let [kb2 (v/open-kb {:backend :disk-snapshot :dir dir})]
        (try
          (is (= {} (kb/write-hazards kb2)))
          (is (= ['(dog Rex)] (dogs kb2)))
          (is (not= "stale" (:source (stamp dir))))
          (finally (v/close! kb2))))
      (finally
        (.countDown release)
        (rm-rf! dir)))))

(deftest recover-during-the-rebuild-runs-it-on-the-calling-thread
  (let [dir (store!)
        [kb ^CountDownLatch reached ^CountDownLatch release] (open-held dir)]
    (try
      (is (.await reached 30 TimeUnit/SECONDS))
      (v/recover kb)
      (is (= {} (kb/write-hazards kb)))
      (is (= ['(dog Rex)] (dogs kb)))
      (is (not= "stale" (:source (stamp dir))))
      (finally
        (.countDown release)
        (v/close! kb)
        (rm-rf! dir)))))

(deftest an-image-declined-for-its-records-is-recovered-under-background-too
  (let [dir (store!)]
    (restamp! dir :records :moved)
    (let [kb (v/open-kb {:backend :disk-snapshot :dir dir :recover? :background})]
      (try
        (is (= {} (kb/write-hazards kb)) "the open recovered, so nothing is being rebuilt")
        (is (= ['(dog Rex)] (dogs kb)))
        (is (not= :moved (:records (stamp dir))))
        (finally
          (v/close! kb)
          (rm-rf! dir))))))
