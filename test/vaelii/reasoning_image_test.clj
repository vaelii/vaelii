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
            [taoensso.nippy :as nippy]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as ri]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu])
  (:import [java.io DataInputStream DataOutputStream File RandomAccessFile]
           [java.nio.file CopyOption Files StandardCopyOption]))

(defn- copy-dir! [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        ;; A store still open on `from` renames a temp file away between the listing and
        ;; the copy (the durability daemon's `counters.nippy` write), and a file gone by
        ;; then is one the directory no longer holds.
        (try
          (Files/copy (.toPath f) (.toPath t)
                      ^"[Ljava.nio.file.CopyOption;"
                      (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))
          (catch java.nio.file.NoSuchFileException _ nil))))))

(defn- manifest ^File [dir] (io/file dir "reasoning" "manifest.edn"))

(defn- manifest-text [dir] (let [f (manifest dir)] (when (.exists f) (slurp f))))

(def ^:private ^java.util.Map opened
  "KB → whether its open installed an image, recorded by `open`.  Weak-keyed, so the map
  holds no KB a test has finished with."
  (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn- open
  "Open `dir` as a `:disk-snapshot` KB and record whether the open installed an image.  An
  install leaves the manifest as it was; a recover writes a fresh image, whose manifest
  carries a new `:written-at`, so an unchanged manifest means the image was installed.
  `recover?` is the open's `:recover?`, the default when omitted."
  ([dir] (open dir nil))
  ([dir recover?]
   (let [before (manifest-text dir)
         kb     (v/open-kb (cond-> {:backend :disk-snapshot :dir dir}
                             recover? (assoc :recover? recover?)))]
     (.put opened kb (and (some? before) (= before (manifest-text dir))))
     kb)))

(defn- installed? [kb] (.get opened kb))

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

(defn- network [kb] (dissoc (jtms/snapshot (reasoning/tms kb)) :touched :touched-in :touched-new :touched-out))

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
  (let [ref (tu/tmpdir "vaelii-reasoning-image-")]
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
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
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
        (finally (tu/rm-rf! dir))))))

(deftest a-clash-with-a-derived-side-reinstalls
  (tu/with-snapshot-platform
    ;; A clash report lists each side's supporting justifications, and a derived side has
    ;; some: the image writes them as field maps, since its reader refuses a class name,
    ;; and reads them back into the records the writer held.
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)]
          ;; before `content!`, whose disjointness arrives last and so settles the clash
          ;; rather than refusing the fact that makes it
          (v/assert kb '(set/forwardRule (implies (and (kitten ?x)) (cat ?x))) 'CxUniverse)
          (v/assert kb '(kitten Tom) 'CxUniverse {:strength :default})
          (v/assert kb '(dog Tom) 'CxUniverse {:strength :default})
          (content! kb)
          ;; the reports are read before the state is taken
          (let [sides  (mapcat :sides (v/contradictions kb))
                closed (whole kb)]
            (is (some #(seq (:justifications %)) sides) "a side of some clash is derived")
            (v/close! kb)
            (let [a (open dir)]
              (try
                (is (installed? a) "the image was installed")
                (same-as! closed (whole a))
                (finally (v/close! a))))))
        (finally (tu/rm-rf! dir))))))

(deftest an-image-a-recover-wrote-reinstalls-that-recover
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
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
        (finally (tu/rm-rf! dir))))))

(deftest an-installed-kb-believes-what-a-recover-of-its-records-believes
  (tu/with-snapshot-platform
    ;; The labels are order independent, so an image written by a KB built assert by assert
    ;; carries the labels a recover computes.  The network's depths and the settle's readings
    ;; are the writer's, and a recover rebuilds those rather than reading them, so only belief
    ;; is compared here — the two tests above hold the rest.
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
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
            (finally (v/close! a) (v/close! b) (tu/rm-rf! ref))))
        (finally (tu/rm-rf! dir))))))

(defn- inherited-reports [kb]
  (into #{} (comp (filter #(= :inherited (:kind %))) (map (juxt :sentence :priority)))
        (concat (v/conflicts kb) (v/contradictions kb))))

(deftest an-installed-kb-s-first-settle-asks-the-claims-its-own-writes-store
  (tu/with-snapshot-platform
    ;; The second session installs the first's image and settles once, so its discovery
    ;; memo, imaged at the close, holds a mark taken in its network's first settle.  The
    ;; third session's network is a fresh one, and its first settle is the denial's.
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")
          U   'CxUniverse
          mono {:strength :monotonic}]
      (try
        (let [kb (open dir)]
          (v/assert kb '(binary_predicate carriesLoad) U)
          (v/assert kb '(transitiveInArgInverse carriesLoad 1 genl) U mono)
          (v/assert kb '(genl hauler_kind animal) U)
          (v/assert kb '(genl cart_kind hauler_kind) U mono)
          (v/assert kb '(carriesLoad hauler_kind Bone1) U mono)
          (v/close! kb))
        (let [kb (open dir)]
          (is (installed? kb))
          (v/assert kb '(carriesLoad hauler_kind Bone2) U mono)
          (v/close! kb))
        (let [a       (open dir)
              [b ref] (recovered-copy dir)]
          (try
            (is (installed? a))
            (doseq [k [a b]] (v/assert k '(not (carriesLoad cart_kind Bone1)) U mono))
            (is (seq (inherited-reports b)) "the denial clashes with the inherited claim")
            (is (= (inherited-reports b) (inherited-reports a)))
            (finally (v/close! a) (v/close! b) (tu/rm-rf! ref))))
        (finally (tu/rm-rf! dir))))))

(deftest an-installed-kb-s-first-read-takes-the-taxonomy-s-own-separation-tables
  (tu/with-snapshot-platform
    ;; The image holds the membership candidates' separation inputs and the taxonomy's
    ;; separation tables as two read-back copies, equal and not identical.  The first read
    ;; takes the taxonomy's, so a later read compares the two by identity, not entry by
    ;; entry.
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)] (content! kb) (v/close! kb))
        (let [a (open dir)]
          (try
            (is (installed? a))
            (decide/synced a)
            (is (every? true? (map identical?
                                   (tax/separation-inputs (reasoning/taxonomy a))
                                   (:vaelii.impl.decide.membership/sep-inputs
                                    @(reasoning/nogood-candidates a)))))
            (finally (v/close! a))))
        (finally (tu/rm-rf! dir))))))

(deftest a-write-then-a-close-refreshes-the-image
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
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
        (finally (tu/rm-rf! dir))))))

(defn- rewrite-manifest! [dir f]
  (spit (manifest dir) (pr-str (f (edn/read-string (slurp (manifest dir)))))))

(defrecord Planted [a])

(defn- truncate! [^File f]
  (with-open [r (RandomAccessFile. f "rw")] (.setLength r (quot (.length r) 2))))

(def ^:private spoilers
  [["the records moved under it"
    (fn [dir]
      (let [aside (tu/tmpdir "vaelii-reasoning-image-")]
        (copy-dir! (str dir "/reasoning") aside)
        (let [kb (open dir)] (v/assert kb '(dog Muffet) 'CxUniverse {:strength :default}) (v/close! kb))
        (tu/rm-rf! (str dir "/reasoning"))
        (copy-dir! aside (str dir "/reasoning"))
        (tu/rm-rf! aside)))]
   ["another source digest"
    (fn [dir] (rewrite-manifest! dir #(assoc % :source "0")))]
   ["another image layout"
    (fn [dir] (rewrite-manifest! dir #(update % :format dec)))]
   ["another policy"
    (fn [dir] (rewrite-manifest! dir #(update-in % [:policy :assertive-arg-types] not)))]
   ["another forced-monotonic set"
    (fn [dir] (rewrite-manifest! dir #(update-in % [:policy :forced-monotonic] conj
                                                 '[forced_monotonic_predicate likes])))]
   ["a truncated network section"
    (fn [dir] (truncate! (io/file dir "reasoning" "network.bin")))]
   ["a truncated state section"
    (fn [dir] (truncate! (io/file dir "reasoning" "state.nippy")))]
   ["a state section naming a class"
    (fn [dir]
      (let [f  (io/file dir "reasoning" "state.nippy")
            st (with-open [i (DataInputStream. (io/input-stream f))] (nippy/thaw-from-in! i))]
        (with-open [o (DataOutputStream. (io/output-stream f))]
          (nippy/freeze-to-out! o (assoc-in st [:taxonomy ::planted] (->Planted 1))))))]])

(deftest a-default-open-keeps-an-image-written-under-another-source
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)] (content! kb) (v/close! kb))
        (rewrite-manifest! dir #(assoc % :source "0"))
        (let [a (open dir)
              [b ref] (recovered-copy dir)]
          (try
            (is (installed? a) "the image was installed, not recovered past")
            (is (not (:stale-belief (v/write-hazards a))))
            (is (= (belief b) (belief a)) "it holds the labels a recover derives")
            (finally (v/close! a) (v/close! b) (tu/rm-rf! ref))))
        (is (= "0" (:source (edn/read-string (manifest-text dir))))
            "the close keeps the source the belief was derived under")
        (finally (tu/rm-rf! dir))))))

(defn- strip-argument-family!
  "Rewrite the image in `dir` as a build without the argument family wrote it: its
  candidate index holds none of `vaelii.impl.decide.argument`'s keys, and its manifest
  names another source."
  [dir]
  (let [f  (io/file dir "reasoning" "state.nippy")
        st (with-open [i (DataInputStream. (io/input-stream f))] (nippy/thaw-from-in! i))
        st (update-in st [:atoms :nogood-candidates]
                      #(into {} (remove (fn [[k _]] (and (keyword? k) (= "vaelii.impl.decide.argument" (namespace k))))) %))]
    (with-open [o (DataOutputStream. (io/output-stream f))] (nippy/freeze-to-out! o st))
    (rewrite-manifest! dir #(assoc % :source "0"))))

(deftest an-image-without-the-argument-family-installs-with-no-whole-argument-read
  (tu/with-snapshot-platform
    (let [dir   (tu/tmpdir "vaelii-reasoning-image-")
          reads (atom 0)
          all   @#'checks/all-declarations]
      (try
        (let [kb (open dir)]
          (content! kb)
          (v/assert kb '(arg owns 1 animal) 'CxUniverse {:strength :monotonic})
          (v/assert kb '(owns Fido Bone) 'CxUniverse)
          (v/close! kb))
        (strip-argument-family! dir)
        (with-redefs [checks/all-declarations (fn [kb] (swap! reads inc) (all kb))]
          (let [a (open dir)]
            (try
              (is (installed? a))
              (is (zero? @reads) "the install reads no declaration")
              (v/assert a '(owns Rex Bone) 'CxUniverse)
              (is (zero? @reads) "the first settle reads no declaration whole")
              (let [[b ref] (recovered-copy dir)]
                (try (is (= (belief b) (belief a)) "it believes what a recover of its records believes")
                     (finally (v/close! b) (tu/rm-rf! ref))))
              (finally (v/close! a)))))
        (finally (tu/rm-rf! dir))))))

(deftest the-image-policy-names-the-forced-monotonic-declarations
  (tu/with-snapshot-platform
    ;; the forced sets an image carries were computed under the forced-monotonic set the
    ;; declarations give, so the image's `:policy` carries those declarations and an image
    ;; under other ones is declined
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb     (open dir)
              declared #(:forced-monotonic (:policy (ri/manifest-for kb nil)))]
          (try
            (is (= [] (declared)))
            (v/assert kb '(forced_monotonic_predicate likes) 'CxUniverse)
            (is (= '[[forced_monotonic_predicate likes CxUniverse]] (declared)))
            (finally (v/close! kb))))
        (finally (tu/rm-rf! dir))))))

(deftest a-stale-or-torn-image-is-declined-and-the-open-recovers
  (tu/with-snapshot-platform
    (doseq [[label spoil!] spoilers]
      (testing label
        (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
          (try
            (let [kb (open dir)] (content! kb) (v/close! kb))
            (spoil! dir)
            ;; `:auto`, which declines an image written under other engine source; the
            ;; default keeps that one (the test after this)
            (let [a (open dir :auto)
                  [b ref] (recovered-copy dir)]
              (try
                (is (not (installed? a)) "the image was declined")
                (same-as! (whole b) (whole a))
                (finally (v/close! a) (v/close! b) (tu/rm-rf! ref))))
            (finally (tu/rm-rf! dir))))))))

(deftest a-kb-running-its-own-code-takes-no-image
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)]
          (content! kb)
          (v/add-evaluatable kb 'evenSum (fn [a b] (even? (+ a b))))
          (is (= :provers-registered (ri/refusal kb)))
          (is (nil? (ri/save! kb)))
          (v/close! kb))
        (is (not (.exists (manifest dir))) "nor does its close write one")
        (finally (tu/rm-rf! dir))))))

(deftest a-kb-registering-a-shipped-reasoner-takes-an-image-the-next-open-installs
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)]
          (content! kb)
          (v/add-reasoner kb :allen)
          (is (nil? (ri/refusal kb)))
          (is (= [:allen] (:reasoners (:policy (ri/save! kb)))))
          (v/close! kb))
        (let [before (manifest-text dir)
              kb     (v/open-kb {:backend :disk-snapshot :dir dir :reasoners :stored})]
          (try
            (is (= before (manifest-text dir)) "the open installed the image")
            (finally (v/close! kb))))
        (finally (tu/rm-rf! dir))))))

(def ^:private other-solver
  "A `Solver` value that is not the local one and solves as it does."
  (reify solve-types/Solver
    (solve [_ program] (solve-types/solve solve/local-solver program))))

(deftest an-open-installs-the-image-before-set-solver-runs
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)] (content! kb) (v/close! kb))
        (let [kb (open dir)]
          (try
            (is (installed? kb) "every KB opens on the default solver")
            (v/set-solver kb other-solver)
            (is (= :solver-set (ri/refusal kb)))
            (finally (v/close! kb))))
        (finally (tu/rm-rf! dir))))))

(deftest a-kb-holding-another-solver-writes-no-image-and-the-next-open-recovers
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)] (content! kb) (v/close! kb))
        (let [before (manifest-text dir)
              kb     (open dir)]
          (v/set-solver kb other-solver)
          (v/assert kb '(dog Muffet) 'CxUniverse)
          (v/close! kb)
          (is (= before (manifest-text dir)) "the close wrote no image"))
        (let [kb (v/open-kb {:backend :disk-snapshot :dir dir :recover? false})]
          (try
            (is (= :records-differ (:reason (ri/install! kb))))
            (finally (v/close! kb))))
        (let [a       (open dir)
              [b ref] (recovered-copy dir)]
          (try
            (is (not (installed? a)) "the open recovered")
            (same-as! (whole b) (whole a))
            (finally (v/close! a) (v/close! b) (tu/rm-rf! ref))))
        (finally (tu/rm-rf! dir))))))

(deftest no-image-is-written-while-a-settle-decides-the-belief
  (tu/with-snapshot-platform
    ;; The writer's settle is parked before its discovery, and the image write on this
    ;; thread declines: the manifest covers the records, and a settle moves belief without
    ;; writing one, so an image of a network a settle is deciding would pass the next open's
    ;; check and install belief no settled KB held.
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb      (open dir)
              _       (content! kb)
              parked  (promise)
              release (promise)
              orig    @#'discovery/discover-inherited!
              armed   (atom true)]
          (with-redefs [discovery/discover-inherited!
                        (fn [& args]
                          (when (compare-and-set! armed true false)
                            (deliver parked true)
                            @release)
                          (apply orig args))]
            (let [w (future (v/assert kb '(dog Spot) 'CxUniverse))]
              (try
                (is (true? (deref parked 10000 false)) "the settle never reached its discovery")
                (is (nil? (ri/save! kb)) "an image was written while a settle held the network")
                (finally (deliver release true) (deref w 10000 nil)))))
          (is (some? (ri/save! kb)) "the settle has published, and the image is written")
          (v/close! kb))
        (finally (tu/rm-rf! dir))))))

(deftest a-kb-whose-belief-does-not-cover-its-records-writes-no-image
  (tu/with-snapshot-platform
    (testing "a loader declared the belief unbuilt"
      (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
        (try
          (let [kb (open dir)]
            (content! kb)
            (kb/note-hazards! kb {:no-belief true})
            (is (nil? (ri/save! kb)))
            (v/close! kb))
          (is (not (.exists (manifest dir))))
          (finally (tu/rm-rf! dir)))))
    (testing "a record with no node and no inert mark"
      (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
        (try
          (let [kb (open dir)]
            (content! kb)
            (let [h (v/assert-inert kb '(dog Spot) 'CxUniverse)]
              (p/put-provenance (:records kb) h (dissoc (p/get-provenance (:records kb) h) :inert)))
            (is (nil? (ri/save! kb)))
            (v/close! kb))
          (is (not (.exists (manifest dir))))
          (finally (tu/rm-rf! dir)))))))

(deftest an-inert-sentex-is-imaged-and-reopens-stored-and-not-believed
  (tu/with-snapshot-platform
    ;; neither `assert-inert` nor a recover makes a node for the inert record
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)]
          (content! kb)
          (v/assert-inert kb '(dog Spot) 'CxUniverse)
          (is (some? (ri/save! kb)))
          (v/close! kb))
        (let [a (open dir)
              [b ref] (recovered-copy dir)]
          (try
            (is (installed? a))
            (is (= (belief b) (belief a)))
            (is (= (set (keys (:nodes (network b)))) (set (keys (:nodes (network a))))))
            (is (false? (get (belief a) ['(dog Spot) 'CxUniverse])))
            (finally (v/close! a) (v/close! b) (tu/rm-rf! ref))))
        (finally (tu/rm-rf! dir))))))

(deftest every-kb-atom-is-imaged-or-named-as-left-alone
  (let [kb    (v/open-kb {:backend :memory :space [::atoms] :recover? false})
        atoms (into #{} (keep (fn [[k x]] (when (instance? clojure.lang.IAtom x) k)))
                    (concat kb (reasoning/of kb)))]
    (is (= atoms (set/union (set (ri/state-atoms)) (ri/unimaged-atoms)))
        "a new KB atom must be carried by the image or named in `unimaged-atoms`")))

(defn- export-import
  "Build `content!` in a `:disk-snapshot` KB, run `before-export!` on it, export it to a
  dump, spoil the dump with `spoil!`, and import it into a fresh `:disk-log` KB.  Calls
  `f` with the exporter, the importer, the export summary and the import summary."
  [before-export! spoil! f]
  (let [src (tu/tmpdir "vaelii-reasoning-image-") dump (str (tu/tmpdir "vaelii-reasoning-image-") "/dump") dst (tu/tmpdir "vaelii-reasoning-image-")]
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
      (finally (tu/rm-rf! src) (tu/rm-rf! (.getParent (io/file dump))) (tu/rm-rf! dst)))))

(deftest a-dump-carries-the-image-and-an-import-installs-it
  (tu/with-snapshot-platform
    (export-import
     (fn [_]) (fn [_])
     (fn [a b ex im]
       (is (= :written (:reasoning-image ex)))
       (is (= {:reasoning :installed} (:reasoning-image im)))
       (same-as! (whole a) (whole b))))))

(deftest an-import-into-a-kb-that-set-a-solver-declines-the-dump-s-image
  (tu/with-snapshot-platform
    (let [src  (tu/tmpdir "vaelii-reasoning-image-")
          dump (str (tu/tmpdir "vaelii-reasoning-image-") "/dump")
          dst  (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [a (open src)]
          (content! a)
          (v/export! a dump)
          (let [b (doto (v/open-kb {:backend :disk-log :dir dst}) (v/set-solver other-solver))]
            (try
              (is (= {:reasoning :recovered :reason :solver-set} (:reasoning-image (v/import! b dump))))
              (is (= (belief a) (belief b)) "the import recovered from the records")
              (finally (v/close! a) (v/close! b)))))
        (finally (tu/rm-rf! src) (tu/rm-rf! (.getParent (io/file dump))) (tu/rm-rf! dst))))))

(deftest a-dump-image-under-another-source-is-installed-and-trusted
  (tu/with-snapshot-platform
    (export-import
     (fn [_])
     (fn [dump]
       (let [f (io/file dump "reasoning" "manifest.edn")]
         (spit f (pr-str (assoc (edn/read-string (slurp f)) :source "0")))))
     (fn [a b _ im]
       (is (= {:reasoning :installed :trusted "0"} (:reasoning-image im)))
       (is (not (:stale-belief (v/write-hazards b))) "a trusted image refuses no write")
       (same-as! (whole a) (whole b))))))

(deftest a-kb-running-its-own-code-exports-no-image
  (tu/with-snapshot-platform
    (export-import
     (fn [a] (v/add-evaluatable a 'evenSum (fn [x y] (even? (+ x y)))))
     (fn [_])
     (fn [a b ex im]
       (is (= :not-writable (:reasoning-image ex)))
       (is (= {:reasoning :recovered :reason :absent} (:reasoning-image im)))
       (is (= (belief a) (belief b)))))))

(deftest a-dump-written-while-the-kb-moved-carries-no-image
  ;; The network is read after the walks and written with their fingerprints.  A write
  ;; between the two — here from the export's own progress callback, once the sentexes
  ;; have streamed — would install on import as belief the streamed records never had:
  ;; the premise is in the dump and OUT in the network.
  (let [dir  (tu/tmpdir "vaelii-reasoning-image-")
        dump (str dir "/dump")
        open (fn [tag] (v/open-kb {:backend :memory :space [::moved-dump tag] :recover? false}))
        a    (open :a)
        _    (v/assert-rule a '[(dog ?x)] '(animal ?x) 'CxUniverse {:direction :forward})
        hs   (mapv #(v/assert a (list 'dog (symbol (str "Dog" %))) 'CxUniverse) (range 3))
        done (atom false)]
    (try
      (let [ex (v/export! a dump {:chunk-size 1
                                  :on-progress (fn [{:keys [phase]}]
                                                 (when (and (= :justifications phase)
                                                            (compare-and-set! done false true))
                                                   (v/retract! a (first hs))))})
            b  (open :b)
            im (v/import! b dump)]
        (is @done "the retraction ran mid-export")
        (is (= :not-writable (:reasoning-image ex)))
        (is (= {:reasoning :recovered :reason :absent} (:reasoning-image im)))
        (is (v/ask? b '(dog Dog0) 'CxUniverse)
            "the premise the dump streamed is believed, as a recover of it believes it")
        (is (v/ask? b '(animal Dog0) 'CxUniverse) "and so is what it derives")
        (doseq [kb [a b]] (v/clear! kb)))
      (finally (tu/rm-rf! dir)))))

(deftest the-records-fingerprint-covers-the-justifications
  (tu/with-snapshot-platform
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb   (open dir)
              _    (content! kb)
              recs (:records kb)
              fp   (drs/reasoning-fingerprint recs)]
          (try
            (is (= (count (p/justification-ids recs)) (get-in fp [:justifications :count])))
            (testing "a justification stored over unchanged sentexes moves the fingerprint"
              (let [[a c] (take 2 (sort (p/sentex-ids recs)))]
                (p/put-justification recs (jtms/->just (p/next-id recs) 'rule [a] c {} :default))
                (is (= (:sentexes fp) (:sentexes (drs/reasoning-fingerprint recs))))
                (is (not= (:justifications fp) (:justifications (drs/reasoning-fingerprint recs))))))
            (finally (v/close! kb))))
        (finally (tu/rm-rf! dir))))))

(deftest a-cleared-store-declines-the-image-of-the-records-it-held
  (tu/with-snapshot-platform
    ;; `clear!` truncates the logs, so records of the same byte lengths refill the old slots
    ;; exactly, and the store below differs from the one the image describes in content
    ;; alone.  The epoch the wipe mints is the part of the fingerprint that separates the two.
    (let [dir   (tu/tmpdir "vaelii-reasoning-image-")
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
        (finally (tu/rm-rf! dir))))))

(defn- rewrite-state!
  "Replace the image's `state.nippy` in `dir` with `f` of its thawed content, and the
  manifest's record of its length to match."
  [dir f]
  (let [sf (io/file dir "reasoning" "state.nippy")
        st (with-open [i (DataInputStream. (io/input-stream sf))] (nippy/thaw-from-in! i))]
    (with-open [o (DataOutputStream. (io/output-stream sf))]
      (nippy/freeze-to-out! o (f st)))
    (rewrite-manifest! dir #(assoc-in % [:bytes :state] (.length sf)))))

;; `(dog Fred)` withholds the mint `(animal Fred)` that `(parentOf Fred Mary)` entails, and
;; its retraction under `special/*release-withheld?*` false leaves that mint owed
(defn- owe-a-release! [kb]
  (binding [argument/*assertive-arg-types?* true checks/*prune-subsumed-mints?* true]
    (doseq [s '[(genl animal thing) (genl dog animal) (arg parentOf 1 animal)
                (dog Fred) (parentOf Fred Mary)]]
      (v/assert kb s 'CxUniverse))
    (binding [special/*release-withheld?* false]
      (v/retract! kb (v/handle-of kb '(dog Fred) 'CxUniverse)))))

(deftest the-image-carries-the-owed-releases-and-an-image-without-them-installs
  (tu/with-snapshot-platform
    (binding [argument/*assertive-arg-types?* true checks/*prune-subsumed-mints?* true]
      (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
        (try
          (let [kb (open dir)]
            (owe-a-release! kb)
            (is (= 1 (v/owed-releases kb)))
            (v/close! kb))
          (let [a (open dir)]
            (try
              (is (installed? a))
              (is (= 1 (v/owed-releases a)) "a close and a reopen keep the debt")
              (is (= 1 (:released (v/release-withheld! a))))
              (is (true? (get (belief a) ['(animal Fred) 'CxUniverse])))
              (finally (v/close! a))))
          (rewrite-state! dir #(update % :atoms dissoc :mint-queues))
          (let [b (open dir)]
            (try
              (is (installed? b) "an image an earlier build wrote without the queue installs")
              (is (zero? (v/owed-releases b)))
              (finally (v/close! b))))
          (finally (tu/rm-rf! dir)))))))

;; A value whose thaw throws an `OutOfMemoryError` while `heap-short?` holds, as a thaw
;; does when the heap runs out under it, and nippy wraps the error as it wraps that one.
(deftype HeapProbe [])

(def ^:private heap-short? (atom false))

#_{:clj-kondo/ignore [:unresolved-symbol]}
(nippy/extend-freeze HeapProbe ::heap-probe [_probe out] (.writeByte out 0))

#_{:clj-kondo/ignore [:unresolved-symbol]}
(nippy/extend-thaw ::heap-probe [in]
                   (.readByte in)
                   (when @heap-short? (throw (OutOfMemoryError. "Java heap space")))
                   nil)

(deftest a-heap-failure-in-an-install-is-thrown-and-the-image-is-kept
  (tu/with-snapshot-platform
    ;; An image reported unreadable is one an operator deletes, and the recover a declined
    ;; image starts needs more heap than the install that ran out.
    (doseq [[label plant] [["in the state section"
                            #(assoc-in % [:taxonomy ::heap-probe] (->HeapProbe))]]]
      (testing label
        (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
          (try
            (let [kb (open dir)] (content! kb) (v/close! kb))
            (rewrite-state! dir plant)
            (let [before (manifest-text dir)]
              (is (thrown? OutOfMemoryError
                           (try (reset! heap-short? true)
                                (v/open-kb {:backend :disk-snapshot :dir dir})
                                (finally (reset! heap-short? false)))))
              (is (= before (manifest-text dir)) "the open wrote no image over it"))
            (let [kb (open dir)]
              (try (is (installed? kb) "the next open installs it")
                   (finally (v/close! kb))))
            (finally (tu/rm-rf! dir))))))))

(deftest a-heap-failure-writing-an-image-keeps-the-image-it-had
  (tu/with-snapshot-platform
    ;; A close or a seal that runs out of heap while it writes the sections leaves the
    ;; directory's image installable, and leaves no temp file beside it.
    (doseq [[label v] [["in the network section" #'dense/write-image]
                       ["in the state section" #'ri/state-of]]]
      (testing label
        (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
          (try
            (let [kb (open dir)] (content! kb) (v/close! kb))
            (let [before (manifest-text dir)
                  kb     (open dir)]
              (try
                (is (installed? kb))
                (with-redefs-fn {v (fn [& _] (throw (OutOfMemoryError. "Java heap space")))}
                  #(is (nil? (ri/save! kb)) "the failed write is logged and returns nil"))
                (is (= before (manifest-text dir)) "the image it had is in place")
                (is (= #{"manifest.edn" "network.bin" "state.nippy"}
                       (set (.list (io/file dir "reasoning")))))
                (finally (v/close! kb))))
            (let [kb (open dir)]
              (try (is (installed? kb) "the next open installs it")
                   (finally (v/close! kb))))
            (finally (tu/rm-rf! dir))))))))

(defn- repeats
  "`{:symbol n :long n}`: for each class, how many more objects of it `x` holds, counted by
  identity, than distinct values.  Atoms are read through."
  [x]
  (let [seen (java.util.IdentityHashMap.)
        objs {:symbol (java.util.IdentityHashMap.) :long (java.util.IdentityHashMap.)}]
    (letfn [(walk [x]
              (cond
                (symbol? x)                   (.put ^java.util.Map (:symbol objs) x true)
                (instance? Long x)            (.put ^java.util.Map (:long objs) x true)
                (not (or (coll? x) (instance? clojure.lang.IAtom x))) nil
                (.containsKey seen x)         nil
                :else (do (.put seen x true)
                          (cond (instance? clojure.lang.IAtom x) (walk @x)
                                (map? x) (run! (fn [[k v]] (walk k) (walk v)) x)
                                :else    (run! walk x)))))]
      (walk x))
    (update-vals objs (fn [^java.util.Map m] (- (.size m) (count (set (.keySet m))))))))

(deftest an-installed-image-holds-one-object-per-symbol-and-handle-it-repeats
  (tu/with-snapshot-platform
    ;; The KB that writes an image names a symbol or a handle with one object wherever it
    ;; repeats, and so does the KB that installs it.  The network's snapshot boxes its
    ;; handles as it reads them, so only its symbols are counted.
    (let [dir (tu/tmpdir "vaelii-reasoning-image-")]
      (try
        (let [kb (open dir)]
          (content! kb)
          ;; a dilemma per context, so the network holds a `nogood` informant per clash, and
          ;; handles past the boxed `Long`s the JVM caches (-128 to 127)
          (doseq [i (range 64) :let [r (symbol (str "CxImgR" i)) x (symbol (str "ImgPet" i))]]
            (v/assert kb (list 'genlCx r 'CxUniverse) 'CxUniverse {:strength :monotonic})
            (v/assert kb (list 'dog x) r {:strength :default})
            (v/assert kb (list 'cat x) r {:strength :default}))
          (v/close! kb))
        (let [kb (open dir)]
          (try
            (is (installed? kb))
            (is (= {:symbol 0 :long 0} (repeats (state kb))))
            (let [net (jtms/snapshot (reasoning/tms kb))]
              (is (< 1 (count (filter #(symbol? (:informant %)) (vals (:justs net))))))
              (is (zero? (:symbol (repeats net)))))
            (finally (v/close! kb))))
        (finally (tu/rm-rf! dir))))))
