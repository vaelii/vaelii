;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reasoning-image-test
  "The reasoning image (`vaelii.impl.reasoning-image`): a `:disk-snapshot` KB writes its
  whole reasoning state beside the records, and the next open installs it in place of a
  recover; an export dump carries one, and an import of the same records installs it.  An
  installed KB holds the network, the taxonomy and the KB atoms of the KB that wrote the
  image, and believes what a recover of the same records believes, before and after the
  same later writes.  An image that no longer describes the records, the source or the
  policies, or whose sections do not read, is declined, and the open or the import
  recovers to the same belief."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as ri]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-reasoning-image-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- copy-dir! [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        (Files/copy (.toPath f) (.toPath t)
                    (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))))))

(defn- manifest ^File [dir] (io/file dir "reasoning" "manifest.edn"))

(defn- manifest-text [dir] (let [f (manifest dir)] (when (.exists f) (slurp f))))

(def ^:private opened
  "KB → whether its open installed an image, recorded by `open`."
  (atom {}))

(defn- open
  "Open `dir` as a `:disk-snapshot` KB and record whether the open installed an image.  An
  install leaves the manifest as it was; a recover writes a fresh image, whose manifest
  carries a new `:written-at`, so an unchanged manifest means the image was installed."
  [dir]
  (let [before (manifest-text dir)
        kb     (v/open-kb {:backend :disk-snapshot :dir dir})]
    (swap! opened assoc kb (and (some? before) (= before (manifest-text dir))))
    kb))

(defn- installed? [kb] (get @opened kb))

(defn- content!
  "A taxonomy edge, a forward rule that fires through it, a monotonic and a defeasible
  membership, and a disjointness between two defaults that settles as a dilemma."
  [kb]
  (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(set/forwardRule (implies (and (animal ?x)) (mortal ?x))) 'CxUniverse)
  (v/assert kb '(dog Rex) 'CxUniverse {:strength :default})
  (v/assert kb '(cat Rex) 'CxUniverse {:strength :default})
  (v/assert kb '(disjoint dog cat) 'CxUniverse {:strength :default})
  (v/assert kb '(dog Fido) 'CxUniverse {:strength :monotonic}))

(defn- belief
  "Belief as content: `{[sentence context] in?}` over every stored sentex."
  [kb]
  (let [recs (:records kb) tms (reasoning/tms kb)]
    (into {} (keep (fn [id] (when-let [s (p/get-sentex recs id)]
                              [[(v/sentence-of s) (:context s)] (jtms/in? tms id)])))
          (p/sentex-ids recs))))

(defn- network [kb] (dissoc (jtms/snapshot (reasoning/tms kb)) :touched :touched-in :touched-new))

(defn- state [kb] (#'ri/state-of kb))

(defn- whole
  "Everything an image carries, read off a live KB: belief, the network and the state."
  [kb]
  {:belief (belief kb) :network (network kb) :state (state kb)})

(defn- same-as! [expected actual]
  (is (= (:belief expected) (:belief actual)) "belief")
  (is (= (:network expected) (:network actual)) "the network, label for label")
  (is (= (:state expected) (:state actual)) "the taxonomy and the KB atoms"))

(defn- recovered-copy
  "Copy `dir` to a fresh directory, drop the copy's manifest, and open it — a KB that
  recovers the same records from scratch.  Returns `[kb copy-dir]`."
  [dir]
  (let [ref (tmpdir)]
    (copy-dir! dir ref)
    (.delete (manifest ref))
    [(open ref) ref]))

(defn- later-writes!
  "A new taxonomy edge the forward rule fires through, a new membership, and the
  retraction of a premise whose conclusion keeps a second witness."
  [kb]
  (v/assert kb '(genl cat animal) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(dog Muffet) 'CxUniverse {:strength :default})
  (v/retract! kb (v/handle-of kb '(dog Rex) 'CxUniverse)))

(deftest a-reopened-kb-holds-the-state-its-writer-closed-with
  (let [dir (tmpdir)]
    (try
      (let [kb     (open dir)
            _      (content! kb)
            closed (whole kb)]
        (v/close! kb)
        (is (.exists (manifest dir)) "the close wrote an image of the KB it built assert by assert")
        (let [a (open dir)]
          (try
            (is (installed? a) "the image was installed")
            (same-as! closed (whole a))
            (finally (v/close! a)))))
      (finally (rm-rf! dir)))))

(deftest an-image-a-recover-wrote-reinstalls-that-recover
  (let [dir (tmpdir)]
    (try
      (let [kb (open dir)] (content! kb) (v/close! kb))
      (.delete (manifest dir))
      (let [kb        (open dir)
            recovered (whole kb)]
        (is (not (installed? kb)) "with no manifest the open recovered, and wrote an image")
        (v/close! kb)
        (let [a (open dir)]
          (try
            (is (installed? a) "the close kept that image: the records had not moved")
            (same-as! recovered (whole a))
            (finally (v/close! a)))))
      (finally (rm-rf! dir)))))

(deftest an-installed-kb-believes-what-a-recover-of-its-records-believes
  ;; The labels are order independent, so an image written by a KB built assert by assert
  ;; carries the labels a recover computes.  The network's depths and the settle's readings
  ;; are the writer's, and a recover rebuilds those rather than reading them, so only belief
  ;; is compared here — the two tests above hold the rest.
  (let [dir (tmpdir)]
    (try
      (let [kb (open dir)] (content! kb) (v/close! kb))
      (let [a (open dir)
            [b ref] (recovered-copy dir)]
        (try
          (is (installed? a))
          (is (not (installed? b)))
          (is (= (belief b) (belief a)))
          (testing "and after the same later writes"
            (doseq [k [a b]] (later-writes! k))
            (is (= (belief b) (belief a))))
          (finally (v/close! a) (v/close! b) (rm-rf! ref))))
      (finally (rm-rf! dir)))))

(deftest a-write-then-a-close-refreshes-the-image
  (let [dir (tmpdir)]
    (try
      (let [kb (open dir)] (content! kb) (v/close! kb))
      (let [kb (open dir)]
        (is (installed? kb))
        (v/assert kb '(dog Muffet) 'CxUniverse {:strength :default})
        (v/close! kb))
      (let [kb (open dir)]
        (try
          (is (installed? kb) "the close rewrote the image over the moved records")
          (is (true? (get (belief kb) ['(dog Muffet) 'CxUniverse])))
          (finally (v/close! kb))))
      (finally (rm-rf! dir)))))

(defn- rewrite-manifest! [dir f]
  (spit (manifest dir) (pr-str (f (edn/read-string (slurp (manifest dir)))))))

(defn- truncate! [^File f]
  (with-open [r (RandomAccessFile. f "rw")] (.setLength r (quot (.length r) 2))))

(def ^:private spoilers
  [["the records moved under it"
    (fn [dir]
      (let [aside (tmpdir)]
        (copy-dir! (str dir "/reasoning") aside)
        (let [kb (open dir)] (v/assert kb '(dog Muffet) 'CxUniverse {:strength :default}) (v/close! kb))
        (rm-rf! (str dir "/reasoning"))
        (copy-dir! aside (str dir "/reasoning"))
        (rm-rf! aside)))]
   ["another source digest"
    (fn [dir] (rewrite-manifest! dir #(assoc % :source "0")))]
   ["another policy"
    (fn [dir] (rewrite-manifest! dir #(update-in % [:policy :arbitrate] not)))]
   ["a truncated network section"
    (fn [dir] (truncate! (io/file dir "reasoning" "network.bin")))]
   ["a truncated state section"
    (fn [dir] (truncate! (io/file dir "reasoning" "state.nippy")))]])

(deftest a-stale-or-torn-image-is-declined-and-the-open-recovers
  (doseq [[label spoil!] spoilers]
    (testing label
      (let [dir (tmpdir)]
        (try
          (let [kb (open dir)] (content! kb) (v/close! kb))
          (spoil! dir)
          (let [a (open dir)
                [b ref] (recovered-copy dir)]
            (try
              (is (not (installed? a)) "the image was declined")
              (same-as! (whole b) (whole a))
              (finally (v/close! a) (v/close! b) (rm-rf! ref))))
          (finally (rm-rf! dir)))))))

(deftest a-kb-running-its-own-code-takes-no-image
  (let [dir (tmpdir)]
    (try
      (let [kb (open dir)]
        (content! kb)
        (v/add-evaluatable kb 'evenSum (fn [a b] (even? (+ a b))))
        (is (= :provers-registered (ri/refusal kb)))
        (is (nil? (ri/save! kb)))
        (v/close! kb))
      (is (not (.exists (manifest dir))) "nor does its close write one")
      (finally (rm-rf! dir)))))

(deftest a-kb-whose-belief-does-not-cover-its-records-writes-no-image
  (testing "a loader declared the belief unbuilt"
    (let [dir (tmpdir)]
      (try
        (let [kb (open dir)]
          (content! kb)
          (kb/note-hazards! kb {:no-belief true})
          (is (nil? (ri/save! kb)))
          (v/close! kb))
        (is (not (.exists (manifest dir))))
        (finally (rm-rf! dir)))))
  (testing "an inert sentex has a record and no node"
    (let [dir (tmpdir)]
      (try
        (let [kb (open dir)]
          (content! kb)
          (v/assert-inert kb '(dog Spot) 'CxUniverse)
          (is (nil? (ri/save! kb)))
          (v/close! kb))
        (is (not (.exists (manifest dir))))
        (finally (rm-rf! dir))))))

(deftest every-kb-atom-is-imaged-or-named-as-left-alone
  (let [kb    (v/open-kb {:space 15 :recover? false})
        atoms (into #{} (keep (fn [[k x]] (when (instance? clojure.lang.Atom x) k)))
                    (concat kb (reasoning/of kb)))]
    (is (= atoms (set/union (set ri/state-atoms) ri/unimaged-atoms))
        "a new KB atom must be carried by the image or named in `unimaged-atoms`")))

(defn- export-import
  "Build `content!` in a `:disk-snapshot` KB, run `before-export!` on it, export it to a
  dump, spoil the dump with `spoil!`, and import it into a fresh `:disk-log` KB.  Calls
  `f` with the exporter, the importer, the export summary and the import summary."
  [before-export! spoil! f]
  (let [src (tmpdir) dump (str (tmpdir) "/dump") dst (tmpdir)]
    (try
      (let [a (open src)]
        (content! a)
        (before-export! a)
        (let [ex (v/export! a dump)
              _  (spoil! dump)
              b  (v/open-kb {:backend :disk-log :dir dst})
              im (v/import! b dump)]
          (try (f a b ex im)
               (finally (v/close! a) (v/close! b)))))
      (finally (rm-rf! src) (rm-rf! (.getParent (io/file dump))) (rm-rf! dst)))))

(deftest a-dump-carries-the-image-and-an-import-installs-it
  (export-import
   (fn [_]) (fn [_])
   (fn [a b ex im]
     (is (= :written (:reasoning-image ex)))
     (is (= {:reasoning :installed} (:reasoning-image im)))
     (same-as! (whole a) (whole b)))))

(deftest a-dump-image-under-another-source-is-declined-and-the-import-recovers
  (export-import
   (fn [_])
   (fn [dump]
     (let [f (io/file dump "reasoning" "manifest.edn")]
       (spit f (pr-str (assoc (edn/read-string (slurp f)) :source "0")))))
   (fn [a b _ im]
     (is (= {:reasoning :recovered :reason :source-differs} (:reasoning-image im)))
     (is (= (belief a) (belief b))))))

(deftest a-kb-running-its-own-code-exports-no-image
  (export-import
   (fn [a] (v/add-evaluatable a 'evenSum (fn [x y] (even? (+ x y)))))
   (fn [_])
   (fn [a b ex im]
     (is (= :not-writable (:reasoning-image ex)))
     (is (= {:reasoning :recovered :reason :absent} (:reasoning-image im)))
     (is (= (belief a) (belief b))))))

(deftest the-records-stamp-covers-the-justifications
  (let [dir (tmpdir)]
    (try
      (let [kb   (open dir)
            _    (content! kb)
            recs (:records kb)
            fp   (drs/reasoning-fingerprint recs)]
        (try
          (is (= (count (p/justification-ids recs)) (get-in fp [:justifications :count])))
          (testing "a justification stored over unchanged sentexes moves the stamp"
            (let [[a c] (take 2 (sort (p/sentex-ids recs)))]
              (p/put-justification recs (jtms/->just (p/next-id recs) 'rule [a] c {} :default))
              (is (= (:sentexes fp) (:sentexes (drs/reasoning-fingerprint recs))))
              (is (not= (:justifications fp) (:justifications (drs/reasoning-fingerprint recs))))))
          (finally (v/close! kb))))
      (finally (rm-rf! dir)))))

(deftest a-cleared-store-declines-the-image-of-the-records-it-held
  ;; `clear!` truncates the logs, so records of the same byte lengths refill the old slots
  ;; exactly, and the store below differs from the one the image describes in content
  ;; alone.  The epoch the wipe mints is the part of the stamp that separates the two.
  (let [dir   (tmpdir)
        strip (fn [fp] (update-vals fp #(dissoc % :epoch)))]
    (try
      (let [kb (open dir)]
        (v/assert kb '(genl dog animal) 'CxUniverse)
        (v/assert kb '(dog Muffet) 'CxUniverse)
        (v/close! kb))
      (let [kb (open dir)]
        (try
          (v/clear! kb)
          (v/assert kb '(genl cat mammal) 'CxUniverse)
          (v/assert kb '(cat Tiddle) 'CxUniverse)
          (let [imaged (:records (ri/read-manifest (io/file dir "reasoning")))
                now    (drs/reasoning-fingerprint (:records kb))]
            (is (= (strip imaged) (strip now)) "the new records refill the old slots")
            (is (not= imaged now) "the epoch separates the two record sets"))
          (let [kb2 (open dir)]
            (is (not (installed? kb2)) "the image was declined")
            (is (v/isa? kb2 'Tiddle 'mammal))
            (is (not (v/isa? kb2 'Muffet 'animal))))
          (finally (v/close! kb))))
      (finally (rm-rf! dir)))))
