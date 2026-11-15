;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.pull-request-test
  "The pull-request vocabulary of CxTra.  `(PullRequestFn ?repository ?number)` names a
  `pull_request` of a `forge_repository`, its status is its membership in the time-varying
  `open_pr`, `merged_pr`, `closed_pr`, `draft_pr` and `ready_pr` kinds,
  `holdsReadyLatch` says whose call it is that a repository's drafts are ready, and a
  grant of `(MergeAccessFn ?repository)` is an access kind below `merge_access`, which
  entails write access over the same repository by default."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private terms
  '[forge_repository pull_request PullRequestFn pullRequestOf open_pr merged_pr closed_pr
    draft_pr ready_pr holdsReadyLatch merge_access MergeAccessFn mergeAccessOf])

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(defn- desk!
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert kb (list 'genlCx ctx CPT) 'CxUniverse))

(tu/deftest-kb each-term-is-stated-in-the-theory-with-one-comment
  (doseq [t terms]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment t '?c) CPT)))
        (str t " carries one comment in the theory")))
  (is (holds-genl 'forge_repository 'digital_artifact CPT))
  (is (holds-genl 'pull_request 'digital_artifact CPT))
  (is (holds-genl 'merge_access 'write_access CPT))
  (is (holds-genl 'merge_access 'resource_access CPT))
  (testing "every position of a relation of two or more arguments is typed"
    (is (holds-ask '(arg pullRequestOf 3 pull_request) CPT))
    (is (holds-ask '(arg holdsReadyLatch 1 person) CPT))
    (is (holds-ask '(arg holdsReadyLatch 2 forge_repository) CPT))
    (is (holds-ask '(genlArg mergeAccessOf 2 merge_access) CPT)))
  (is (holds-ask '(functionCorrespondingPredicate PullRequestFn pullRequestOf 3) CPT))
  (is (holds-ask '(functionCorrespondingPredicate MergeAccessFn mergeAccessOf 2) CPT)))

(tu/deftest-kb who-may-merge-pull-requests-of-a-repository
  (tu/with-terms [CxDesk Repo OtherRepo Maintainer Writer]
    (desk! kb CxDesk)
    (doseq [s [(list 'forge_repository Repo) (list 'forge_repository OtherRepo)
               (list 'human Maintainer) (list 'human Writer)
               (list 'able Maintainer (list 'MergeAccessFn Repo))
               (list 'able Writer (list 'WriteAccessFn Repo))]]
      (v/assert kb s CxDesk))
    (let [mergers (fn [repo]
                    (set (map #(get % '?p)
                              (v/query kb [(list 'mergeAccessOf repo '?k) '(able ?p ?k)]
                                       CxDesk))))]
      (is (= #{Maintainer} (mergers Repo))
          "the grant holder answers; a write grant is not a merge grant")
      (is (= #{} (mergers OtherRepo)) "a grant keeps its repository"))
    (is (holds-ask (list 'able Maintainer (list 'MergeAccessFn Repo)) CxDesk)
        "asked back through the function term")
    (is (holds-ask (list 'able Maintainer 'merge_access) CxDesk))
    (testing "merge access entails write access over the same repository only"
      (is (holds-ask (list 'able Maintainer (list 'WriteAccessFn Repo)) CxDesk))
      (is (not (holds-ask (list 'able Maintainer (list 'WriteAccessFn OtherRepo)) CxDesk))))
    (testing "write access does not entail merge access"
      (is (not (holds-ask (list 'able Writer 'merge_access) CxDesk))))))

(defn- waiting-on
  [kb holder ctx]
  (set (map (juxt #(get % '?r) #(get % '?n))
            (v/query kb [(list 'holdsReadyLatch holder '?r)
                         '(pullRequestOf ?r ?n ?pr) '(draft_pr ?pr)]
                     ctx))))

(tu/deftest-kb which-pull-requests-wait-on-a-latch-holder
  (tu/with-terms [CxDesk Repo OtherRepo Holder Other]
    (desk! kb CxDesk)
    (doseq [s [(list 'forge_repository Repo) (list 'forge_repository OtherRepo)
               (list 'human Holder) (list 'human Other)
               (list 'holdsReadyLatch Holder Repo)
               (list 'holdsReadyLatch Other OtherRepo)
               (list 'ready_pr (list 'PullRequestFn Repo 2))
               (list 'draft_pr (list 'PullRequestFn OtherRepo 3))]]
      (v/assert kb s CxDesk))
    (let [draft (v/assert kb (list 'draft_pr (list 'PullRequestFn Repo 1)) CxDesk)]
      (is (holds-ask (list 'pull_request (list 'PullRequestFn Repo 1)) CxDesk)
          "the function's result type, not an asserted membership")
      (is (= #{[Repo 1]} (waiting-on kb Holder CxDesk))
          "the draft of the holder's repository; not the ready one, not another repository's draft")
      (is (= #{[OtherRepo 3]} (waiting-on kb Other CxDesk)))
      (v/retract! kb draft)
      (v/assert kb (list 'ready_pr (list 'PullRequestFn Repo 1)) CxDesk)
      (is (= #{} (waiting-on kb Holder CxDesk)) "marked ready, it waits on no one"))))

(tu/deftest-kb a-pull-request-is-at-one-stage-at-a-time
  (testing "the status kinds partition pull_request, and open_pr into draft and ready"
    (is (holds-ask '(partition pull_request open_pr merged_pr closed_pr) CPT))
    (is (holds-ask '(partition open_pr draft_pr ready_pr) CPT))
    (doseq [k '[open_pr merged_pr closed_pr]]
      (is (holds-genl k 'pull_request CPT) (str k " is a kind of pull_request")))
    (doseq [k '[draft_pr ready_pr]]
      (is (holds-genl k 'open_pr CPT) (str k " is a kind of open_pr"))))
  (testing "each status kind is time-varying: a pull request changes status and stays itself"
    (doseq [k '[open_pr merged_pr closed_pr draft_pr ready_pr]]
      (is (holds-ask (list 'time_varying_relation k) CPT) (str k))))
  (tu/with-terms [CxDesk Repo]
    (desk! kb CxDesk)
    (v/assert kb (list 'forge_repository Repo) CxDesk)
    (v/assert kb (list 'draft_pr (list 'PullRequestFn Repo 7)) CxDesk)
    (testing "a draft is open, and so neither merged nor closed"
      (is (holds-ask (list 'open_pr (list 'PullRequestFn Repo 7)) CxDesk))
      (is (holds-ask (list 'not (list 'merged_pr (list 'PullRequestFn Repo 7))) CxDesk))
      (is (holds-ask (list 'not (list 'ready_pr (list 'PullRequestFn Repo 7))) CxDesk)))))

(tu/deftest-kb a-merge-only-role-keeps-its-push-exception
  (tu/with-terms [CxDesk Repo Merger]
    (desk! kb CxDesk)
    (doseq [s [(list 'forge_repository Repo) (list 'human Merger)
               (list 'able Merger (list 'MergeAccessFn Repo))
               (list 'set/monotonic (list 'not (list 'able Merger (list 'WriteAccessFn Repo))))]]
      (v/assert kb s CxDesk))
    (testing "a monotonic exception defeats the merge-to-write default for that repository"
      (is (not (holds-ask (list 'able Merger (list 'WriteAccessFn Repo)) CxDesk))))
    (is (holds-ask (list 'able Merger (list 'MergeAccessFn Repo)) CxDesk)
        "the merge grant itself stands")))
