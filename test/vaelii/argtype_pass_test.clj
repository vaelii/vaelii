;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argtype-pass-test
  "`record-arg-types!`: the argument-type pass stopped, resumed, cancelled and run with
  facts set aside over budget ends in the rows one uninterrupted pass ends in
  (docs/argtypes.md, \"The pass over a stored KB\")."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.argtype-pass :as argpass]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file CopyOption Files StandardCopyOption]))

(defmacro ^:private entailing
  "Run the body with the entailment on and subsumed mints withheld."
  [& body]
  `(binding [argument/*assertive-arg-types?* true
             checks/*prune-subsumed-mints?*  true]
     ~@body))

(defn- terms
  "The fixture's terms, fresh."
  []
  (tu/with-terms [q_w q_k q_a q_b q_c q_e q_s q_d q_top q_t cSub cTop bRel dRel
                  X1 X2 X3 X4 X6 Z1 Z2 Y1 Y2 CxW CxE]
    {:q_w q_w :q_k q_k :q_a q_a :q_b q_b :q_c q_c :q_e q_e :q_s q_s :q_d q_d :q_top q_top :q_t q_t
     :cSub cSub :cTop cTop :bRel bRel :dRel dRel :X1 X1 :X2 X2 :X3 X3 :X4 X4 :X6 X6
     :Z1 Z1 :Z2 Z2 :Y1 Y1 :Y2 Y2 :CxW CxW :CxE CxE}))

(defn- build!
  "A store whose facts were loaded around `assert`, so the pass has every mint to draw:
  `genlArg` mints that write `genl` edges and draw their own, a membership mint that draws
  one of its own (`(arg q_w 1 q_k)`), covers refuted by stored
  negations and by denials of a type above, a negation hidden by an except and one
  defeated, and a membership that withholds a general mint.

  The denials of a type above make one admission depend on the order the facts are drawn
  in: `(q_w q_t)` is admitted before the `genl` mint that puts `q_t` under `q_top` and
  refused after it (`argtype_entail_test`'s held-checks reading).  `above?` false leaves
  them out."
  [kb {:keys [q_w q_k q_a q_b q_c q_e q_s q_d q_top q_t cSub cTop bRel dRel
              X1 X2 X3 X4 X6 Z1 Z2 Y1 Y2 CxW CxE above?] :or {above? true}}]
  (let [M {:strength :monotonic}
        U 'CxUniverse]
    (v/assert kb (list 'genlCx CxW U) U)
    (v/assert kb (list 'genlCx CxE CxW) U)
    (doseq [s [(list 'genl q_w 'thing) (list 'genl q_a q_w) (list 'genl q_b q_w)
               (list 'covering q_w q_a q_b) (list 'genl q_s 'thing) (list 'genl q_d 'thing)
               (list 'disjoint q_d q_a) (list 'genl q_top 'thing)
               (list 'arg bRel 1 q_w) (list 'arg dRel 1 q_w)
               (list 'genl q_k 'thing) (list 'arg q_w 1 q_k)
               (list 'genlArg cSub 1 q_d) (list 'genlArg cTop 1 q_top)
               (list 'transitiveInArgInverse q_a 1 'genl) (list 'transitiveInArgInverse q_b 1 'genl)
               (list 'genl q_c q_w) (list 'genl q_e q_w) (list 'covering q_w q_c q_e)
               (list 'transitiveInArgInverse q_c 1 'genl) (list 'transitiveInArgInverse q_e 1 'genl)]]
      (v/assert kb s CxW M))
    (doseq [s (concat [(list 'not (list q_a X1)) (list 'not (list q_b X1)) (list 'not (list q_a X2))
                       (list q_s X3) (list 'not (list q_b X3)) (list 'not (list q_a X4))
                       (list 'not (list q_a X6)) (list 'not (list q_b X6))
                       (list q_a Z1) (list q_b Z2)]
                      (when above? [(list 'not (list q_a q_top)) (list 'not (list q_b q_top))]))]
      (v/assert kb s CxW))
    (v/assert kb (list 'except (list 'sentexHandle (v/assert kb (list 'not (list q_b X4)) CxW))) CxE M)
    (v/assert kb (list q_b X6) CxE M)
    (v/bulk-assert-facts! kb (concat (for [x [X1 X2 X3 q_t Z1 Z2] r [bRel dRel] y [Y1 Y2]] (list r x y))
                                     [(list cSub q_s Y1) (list cTop q_t Y1)])
                          CxW)
    (v/bulk-assert-facts! kb (for [x [X4 X6] r [bRel dRel] y [Y1 Y2]] (list r x y)) CxE)))

(defn- reading
  "What `kb` stores, believes and justifies, handles resolved to content."
  [kb]
  (let [row #(let [sx (p/get-sentex (:records kb) %)] (tu/handle-free kb [(:sentence sx) (:context sx)]))
        hs  (tu/sentex-ids kb)]
    {:stored    (set (map row hs))
     :believed  (set (map row (filter #(v/believed? kb %) hs)))
     :justified (set (for [h hs, j (v/supporting-justifications kb h)]
                       [(row h) (:informant j) (set (map row (:antecedents j)))]))}))

(defn- pass-reading
  "Build the fixture over `t`, run `f` on the KB, and read it."
  [t f]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (entailing
     (build! kb t)
     (let [r (f kb)]
       (assoc (reading kb) :run r :owed (v/arg-types-owed kb))))))

(defn- every-nth
  "A `:stop?` answering true on every `n`th question."
  [n]
  (let [c (volatile! 0)] (fn [] (zero? (rem (long (vswap! c inc)) (long n))))))

(defn- until-complete
  "Call `record-arg-types!` with `opts` until it completes: `[runs last-result]`."
  [kb opts]
  (loop [runs 1]
    (let [r (v/record-arg-types! kb opts)]
      (if (or (:complete? r) (> runs 500)) [runs r] (recur (inc runs))))))

(deftest a-pass-stopped-and-resumed-ends-where-one-uninterrupted-pass-ends
  (let [t    (terms)
        one  (pass-reading t #(v/record-arg-types! % {:budget-ms nil}))
        rows #(select-keys % [:stored :believed :justified])]
    (testing "the uninterrupted pass completes, owes nothing, and records what `record-arg-types` does"
      (is (:complete? (:run one)))
      (is (nil? (:owed one)))
      (is (= (rows one) (rows (pass-reading t v/record-arg-types))))
      (is (< 5 (:recorded (:run one))) "the fixture has mints to draw"))
    (testing "the first run of a stopped pass leaves mints undrawn and the pass owed"
      (let [first-run (pass-reading t #(v/record-arg-types! % {:budget-ms nil :stop? (every-nth 3)}))]
        (is (= :requested (:stopped (:run first-run))))
        (is (some? (:owed first-run)))
        (is (not= (rows one) (rows first-run)))))
    (doseq [n [1 2 3 7]]
      ;; the first step of a run is taken whatever `:stop?` says, so even a stop at every
      ;; boundary moves the pass on
      (testing (str "stopped at every " n "th fact boundary")
        (let [r (pass-reading t #(until-complete % {:budget-ms nil :stop? (every-nth n)}))
              [runs last-run] (:run r)]
          (is (< 3 runs) "it stopped more than three times")
          (is (:complete? last-run))
          (is (nil? (:owed r)))
          (is (= (rows one) (rows r))))))
    (testing "a stop requested from the progress report, as another thread would"
      (let [r (pass-reading t (fn [kb]
                                (until-complete kb {:budget-ms nil :progress-every-ms 0
                                                    :on-progress (fn [_] (v/request-stop! kb))})))]
        (is (< 3 (first (:run r))))
        (is (= (rows one) (rows r)))))
    (testing "a cancel thrown from the progress report, as a browser job's is"
      (let [r (pass-reading t (fn [kb]
                                (let [n (volatile! 0)]
                                  (loop [cancels 0]
                                    (let [out (try (v/record-arg-types!
                                                    kb {:budget-ms nil :progress-every-ms 0
                                                        :on-progress (fn [_]
                                                                       (when (zero? (rem (long (vswap! n inc)) 4))
                                                                         (throw (ex-info "cancel" {:type ::cancel}))))})
                                                   (catch clojure.lang.ExceptionInfo e
                                                     (if (= ::cancel (:type (ex-data e))) ::cancelled (throw e))))]
                                      (if (and (= ::cancelled out) (< cancels 500))
                                        (recur (inc cancels))
                                        [cancels out]))))))]
        (is (< 3 (first (:run r))) "the cancel landed more than three times")
        (is (:complete? (second (:run r))))
        (is (= (rows one) (rows r)))))
    (testing "a request with no pass running is not held"
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (is (false? (v/request-stop! kb)))))))

(deftest a-release-that-throws-is-owed-to-the-next-run
  (let [t       (terms)
        one     (pass-reading t #(v/record-arg-types! % {:budget-ms nil}))
        release special/release-withheld!
        calls   (volatile! 0)
        r       (pass-reading
                 t (fn [kb]
                     (with-redefs [special/release-withheld!
                                   (fn [kb] (if (= 1 (vswap! calls inc)) (throw (ex-info "release" {})) (release kb)))]
                       (let [thrown (try (v/record-arg-types! kb {:budget-ms nil}) nil
                                         (catch clojure.lang.ExceptionInfo e (ex-message e)))
                             owed   (v/arg-types-owed kb)]
                         [thrown owed (v/record-arg-types! kb {:budget-ms nil})]))))
        [thrown owed run] (:run r)]
    (is (= "release" thrown))
    (is (false? (:swept? owed)) "the record written at the throw leaves the release owed")
    (is (= 2 @calls) "the next run releases")
    (is (:complete? run))
    (is (= (select-keys one [:stored :believed :justified]) (select-keys r [:stored :believed :justified])))))

(defn- ticking
  "`(f)` with `budget/now` a counter that moves one per reading, so a budget of `n`
  nanoseconds runs out at the `n`th check of a fact's draw, wherever that falls."
  [f]
  (let [c (atom 0)]
    (with-redefs [budget/now (fn [] (swap! c inc))]
      (f))))

(deftest facts-set-aside-over-budget-and-drawn-again-end-where-one-pass-ends
  ;; A fact set aside is drawn after the facts behind it, so the fixture leaves out the
  ;; admission that depends on the order facts are drawn in (`build!`)
  (let [t    (assoc (terms) :above? false)
        rows #(select-keys % [:stored :believed :justified])
        one  (pass-reading t #(v/record-arg-types! % {:budget-ms nil}))
        mids (volatile! [])]
    (doseq [ticks [2 9 17 19 25 31]]
      (testing (str "a budget of " ticks " checks")
        (let [budget (/ ticks 1e6)
              r (pass-reading t (fn [kb]
                                  (let [swept (ticking #(v/record-arg-types! kb {:budget-ms budget}))
                                        owed  (v/arg-types-owed kb)
                                        mid   (reading kb)
                                        ;; drawn again at the same budget first, which sets
                                        ;; some aside a second time, then with none
                                        again (ticking #(v/record-arg-types! kb {:budget-ms budget
                                                                                 :retry-deferred? true}))
                                        ;; a run that finds nothing owed starts over, so the
                                        ;; last is made only while something is
                                        done  (if (:complete? again)
                                                again
                                                (v/record-arg-types! kb {:budget-ms nil :retry-deferred? true}))]
                                    {:swept swept :owed owed :mid mid :again again :done done})))
              {:keys [swept owed mid done]} (:run r)]
          (is (pos? (:deferred swept)) "facts were set aside")
          (is (:swept? owed))
          (is (every? :phase (:deferred owed)) "each names the part of the checks that ran out")
          (vswap! mids conj (rows mid))
          (is (:complete? done))
          (is (nil? (:owed r)))
          (is (= (rows one) (rows r))))))
    (is (some #(not= (rows one) %) @mids) "the facts set aside left mints undrawn")
    (testing "a fact set aside part-way through its cascade names the mints it brought IN"
      (let [seen (volatile! [])]
        (pass-reading t (fn [kb]
                          (ticking #(v/record-arg-types! kb {:budget-ms (/ 17 1e6)}))
                          (vreset! seen (:deferred (argpass/read-owed kb)))))
        (is (some (comp seq :transitions) @seen))))))

;; ---- a store with a directory ----------------------------------------------------

(defn- copy-dir!
  "Copy `from` into `to` as the files stand, the store on `from` still open: what a
  process killed at this point leaves on disk."
  [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        ;; the durability daemon renames a temp file away between the listing and the copy
        (try (Files/copy (.toPath f) (.toPath t)
                         ^"[Ljava.nio.file.CopyOption;"
                         (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))
             (catch java.nio.file.NoSuchFileException _ nil))))))

(defn- believed
  "Every believed record of `kb` as `[sentence context]`, handles resolved."
  [kb]
  (:believed (reading kb)))

(defn- removed-batch
  "Build the fixture at `dir`, close it, reopen it without belief and remove `(q_a Z1)`,
  which withheld the general mint `(q_w Z1)`: the KB without belief and the batch's seeds."
  [dir t]
  (let [kb (v/open-kb {:backend :disk-log :dir dir})]
    (entailing (build! kb t) (v/record-arg-types kb))
    (v/close! kb))
  (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? false})
        h   (some #(let [sx (p/get-sentex (:records kb2) %)]
                     (when (and (= (list (:q_a t) (:Z1 t)) (:sentence sx)) (= (:CxW t) (:context sx))) %))
                  (tu/sentex-ids kb2))
        r   (v/edit-records! kb2 {:remove [h]})]
    [kb2 (:seeds r)]))

(deftest the-records-path-settles-without-the-pass-and-owes-it-across-a-reopen
  (let [t (terms)
        via-settle (let [dir (tu/tmpdir "vaelii-argpass-")]
                     (try (let [[kb seeds] (removed-batch dir t)]
                            (try (entailing (v/settle-record-edits! kb {:seeds seeds})
                                            (believed kb))
                                 (finally (v/close! kb))))
                          (finally (tu/rm-rf! dir))))
        dir (tu/tmpdir "vaelii-argpass-")]
    (is (contains? via-settle [(list (:q_w t) (:Z1 t)) (:CxW t)])
        "the removal released the mint it withheld")
    (try
      (let [[kb seeds] (removed-batch dir t)
            phases     (volatile! [])]
        (is (some? (v/arg-types-owed kb)) "the removal made the pass owed")
        (entailing
         (let [s (v/settle-record-edits! kb {:seeds seeds :arg-types? false
                                             :on-progress #(vswap! phases conj (:phase %))})]
           (is (:arg-types-owed? s))
           (is (= [:recover :sweep] (distinct @phases)))
           (is (= {} (v/write-hazards kb)) "the KB is settled and writable")
           (is (not (contains? (believed kb) [(list (:q_w t) (:Z1 t)) (:CxW t)]))
               "the released mint waits for the pass")
           (let [r (v/record-arg-types! kb {:budget-ms nil :stop? (every-nth 4)})]
             (is (= :requested (:stopped r))))
           (is (.exists (io/file dir "arg-types-owed.edn")))))
        (v/close! kb))
      (testing "a reopen resumes the pass from the record in the directory"
        (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          (try
            (entailing
             (v/settle-record-edits! kb {:arg-types? false})
             (let [before (:facts (v/arg-types-owed kb))
                   r      (v/record-arg-types! kb {:budget-ms nil})]
               (is (pos? before))
               (is (< (:drawn r) (:total r)) "it drew only what was owed")
               (is (:complete? r)))
             (is (nil? (v/arg-types-owed kb)))
             (is (not (.exists (io/file dir "arg-types-owed.edn"))))
             (is (= via-settle (believed kb))))
            (finally (v/close! kb)))))
      (finally (tu/rm-rf! dir)))))

(deftest a-killed-pass-redraws-from-its-last-commit
  ;; The process dies after a commit, with the mints of the facts after it on disk and
  ;; belief gone: the reopened store is recovered from the records and the pass resumes
  ;; at the record each commit wrote.
  (let [t       (terms)
        dir     (tu/tmpdir "vaelii-argpass-")
        records (volatile! [])
        write   @#'argpass/write-owed!]
    (try
      (let [kb (v/open-kb {:backend :disk-log :dir dir})]
        (entailing
         (build! kb t)
         (with-redefs [argpass/write-owed! (fn [kb o] (when o (vswap! records conj o)) (write kb o))]
           (is (:complete? (v/record-arg-types! kb {:budget-ms nil :commit-every-ms 0}))))
         (let [one (reading kb)]
           (v/close! kb)
           (is (< 3 (count @records)) "the pass committed more than three times")
           (doseq [o (take-nth 3 @records)]
             (testing (str "killed after the commit at " (pr-str (:at o)))
               (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
                 (try
                   (write kb o)
                   (v/settle-record-edits! kb {:arg-types? false})
                   (is (:complete? (v/record-arg-types! kb {:budget-ms nil})))
                   (is (= one (reading kb)))
                   (finally (v/close! kb)))))))))
      (finally (tu/rm-rf! dir)))))

(deftest a-pass-killed-at-a-commit-resumes-from-the-directory-the-commit-left
  ;; The directory is copied after a commit with the store still open, so the copy holds
  ;; what the commit forced to disk and nothing a close writes.  The resumed pass reads
  ;; the copy's record as written against the records it holds.
  (let [t    (terms)
        dir  (tu/tmpdir "vaelii-argpass-")
        dir2 (tu/tmpdir "vaelii-argpass-")]
    (try
      (entailing
       (let [one (let [kb (v/open-kb {:backend :disk-log :dir dir})]
                   (try
                     (build! kb t)
                     (is (= :requested (:stopped (v/record-arg-types! kb {:budget-ms nil :stop? (every-nth 3)}))))
                     (copy-dir! dir dir2)
                     (is (:complete? (second (until-complete kb {:budget-ms nil}))))
                     (reading kb)
                     (finally (v/close! kb))))
             kb  (v/open-kb {:backend :disk-log :dir dir2 :recover? false})]
         (try
           (v/settle-record-edits! kb {:arg-types? false})
           (is (pos? (:facts (v/arg-types-owed kb))))
           (is (:complete? (v/record-arg-types! kb {:budget-ms nil})))
           (is (= one (reading kb)))
           (finally (v/close! kb)))))
      (finally (tu/rm-rf! dir) (tu/rm-rf! dir2)))))

(deftest an-owed-record-ahead-of-the-records-is-refused
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (entailing
     (build! kb (terms))
     (#'argpass/write-owed! kb {:version 1 :drawn #{} :at nil :deferred [] :swept? false
                                :facts 0 :mark (+ 1000000 (long (p/next-id (:records kb))))})
     (is (= :owed-record-ahead
            (:type (ex-data (try (v/record-arg-types! kb) (catch Exception e e))))))
     (is (:complete? (v/record-arg-types! kb {:resume? false :budget-ms nil}))))))

(deftest a-clear-drops-the-owed-record
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (entailing
     (build! kb (terms))
     (v/record-arg-types! kb {:budget-ms nil :stop? (every-nth 3)})
     (is (some? (v/arg-types-owed kb)) "the stopped pass is owed")
     (v/clear! kb)
     (is (nil? (v/arg-types-owed kb)) "the wipe leaves nothing owed"))))

(deftest an-owed-record-of-another-shape-is-refused
  ;; A record this engine cannot read is refused rather than taken for "nothing owed":
  ;; a pass that skipped it would leave every fact it names undrawn.
  (let [dir (tu/tmpdir "vaelii-argpass-")]
    (try
      (let [kb (v/open-kb {:backend :disk-log :dir dir})]
        (try
          (spit (io/file dir @#'argpass/owed-file) (pr-str {:version 99 :drawn #{}}))
          (is (= :unknown-owed-record
                 (:type (ex-data (try (v/arg-types-owed kb) (catch Exception e e))))))
          (finally (v/close! kb))))
      (finally (tu/rm-rf! dir)))))

;; ---- a mint the fact would leave as it is ------------------------------------------

(defn- counting-asks
  "`(f)` with each admission ask of a mint counted: `[result asks]`."
  [f]
  (let [n    (atom 0)
        orig special/inadmissible]
    (with-redefs [special/inadmissible (fn [& args] (swap! n inc) (apply orig args))]
      (let [r (f)] [r @n]))))

(defn- asking-every-mint
  "`(f)` with no mint passed over before its checks."
  [f]
  (with-redefs-fn {#'special/unchanged-mint? (constantly false)
                   #'special/held-mint?      (constantly false)}
    f))

(defn- add-changed!
  "Facts whose mints the store does not hold as the pass would draw them: `(bRel nx Y1)`,
  whose `(q_w nx)` is not stored, and `(bRel ny Y1)`, whose `(q_w ny)` is stored as a
  premise with no support from `arg`."
  [kb {:keys [q_w bRel Y1 CxW]} nx ny]
  (v/assert kb (list q_w ny) CxW)
  (v/bulk-assert-facts! kb [(list bRel nx Y1) (list bRel ny Y1)] CxW))

(deftest a-pass-asks-the-checks-only-of-a-mint-it-would-change
  ;; without the denials of a type above: there `(q_w q_t)` is admitted for the facts
  ;; drawn before the `genl` mint and refused for those after, so a second pass asks it
  ;; again for each fact whose support it lacks
  (tu/with-terms [NX NY]
    (let [t     (assoc (terms) :above? false)
          again #(v/record-arg-types! % {:resume? false :budget-ms nil})
          drawn (fn [kb] (is (:complete? (v/record-arg-types! kb {:budget-ms nil}))))]
      (testing "over a store whose mints are drawn, a second pass asks nothing and changes nothing"
        (tu/with-cleared-kb [kb tu/isolated-fresh]
          (entailing
           (build! kb t)
           (drawn kb)
           (let [before   (reading kb)
                 [r asks] (counting-asks #(again kb))]
             (is (:complete? r))
             (is (zero? asks) "every mint is stored with its support, or withheld")
             (is (zero? (:recorded r)))
             (is (= before (reading kb)))
             (is (pos? (second (counting-asks #(asking-every-mint (fn [] (again kb))))))
                 "where a pass that asks every mint asks")))))
      (let [run  (fn [ask-all?]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     (entailing
                      (build! kb t)
                      (drawn kb)
                      (add-changed! kb t NX NY)
                      (let [[r asks] (counting-asks #(if ask-all? (asking-every-mint (fn [] (again kb))) (again kb)))]
                        (assoc (reading kb) :run r :asks asks)))))
            some (run false)
            all  (run true)
            rows #(select-keys % [:stored :believed :justified])
            {:keys [q_w q_k CxW]} t]
        (testing "a mint not stored, or stored without the fact's support, is asked and drawn"
          (is (pos? (:asks some)))
          (is (< (:asks some) (:asks all)) "and only those are asked")
          (is (contains? (:stored some) [(list q_w NX) CxW]))
          (is (contains? (:stored some) [(list q_k NX) CxW]) "with the mint's own")
          (is (some (fn [[row informant]] (and (= row [(list q_w NY) CxW]) (= 'arg informant)))
                    (:justified some))
              "the premise takes the fact's support"))
        (testing "and the store ends where a pass asking every mint ends"
          (is (= (rows all) (rows some))))))))
