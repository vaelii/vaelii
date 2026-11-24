#!/usr/bin/env python3
"""Tests of perf-owed.py over a scratch repository holding two small harnesses, one engine
namespace and one shipped-KB file. Run: python3 scripts/test_perf_owed.py"""

import importlib.util
import os
import shutil
import subprocess
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("perf_owed", os.path.join(HERE, "perf-owed.py"))
po = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(po)

PERF = """(ns vaelii.bench.perf)

(defn- helper [n] (inc n))

(defn- loads [n] (core-context/load-into n))

(defn- spare [n] n)

(def checks
  [{:name :alpha :claim "spare is named in a string only"
    :sizes [1 2]
    :run (fn [n] (helper n))}
   ;; beta's comment
   {:name :beta
    :run (fn [n] (loads n))}])

(defn -main [] (run! :run checks))
"""

AB = """(ns vaelii.bench.ab)

(defn- fresh [] 1)

(defn genl-read [] (fresh))

(defn starter-load [] (starter/load-into (fresh)))

(def probes
  [#'genl-read
   #'starter-load])
"""

ENGINE = """(ns vaelii.impl.x)

(declare g)

(defn f [] 1)

(defn g [] 2)

(defn dead [] 3)

(defn table-row [] 4)

(def table (mapv (fn [_] (table-row)) (range 3)))

(def ops {:dead 2})

(defmethod shape :k [_] 5)

(defmacro m [x] x)

(def ^:dynamic *flag*
  "Read by f."
  nil)
"""

BRANCHES = """(ns vaelii.impl.y)

(defn k
  "doc"
  [x]
  (let [a (pre x)]
    (if (test? a)
      (when (ok? a)
        (left a)
        (more a))
      (right
        a))))

(defn n [x]
  (mac (left x)
       x))
"""

FILES = {po.PERF: PERF, po.AB: AB, "src/vaelii/impl/x.clj": ENGINE,
         "src/vaelii/impl/y.clj": BRANCHES,
         "resources/kb/upper/a.txt": "(genl dog animal)\n", "README.md": "readme\n"}

TARGETS = ["alpha", "beta", "ab:genl-read", "ab:starter-load"]


def edit(text, old, new):
    """Returns `text` with its one occurrence of `old` replaced by `new`."""
    assert text.count(old) == 1, old
    return text.replace(old, new)


class Repo(unittest.TestCase):
    """A scratch repository at revision `base`, with `po.ROOT` pointed at it."""

    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.dir)
        self.root, po.ROOT = po.ROOT, self.dir
        self.addCleanup(setattr, po, "ROOT", self.root)
        self.git("init", "-q")
        for p, text in FILES.items():
            self.write(p, text)
        self.base = self.commit()

    def git(self, *args):
        return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@example.com",
                               "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null",
                               *args], cwd=self.dir, check=True, capture_output=True,
                              text=True).stdout.strip()

    def write(self, path, text):
        full = os.path.join(self.dir, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as f:
            f.write(text)

    def change(self, path, old, new):
        """Edits `path` in the working tree."""
        self.write(path, edit(FILES[path], old, new))

    def commit(self):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def reach(self, rows, targets=TARGETS, failed=(), lines=None, rev=None, dirty="0"):
        """Writes a reach map at `rev` (default `base`) outside the repository, with the line
        map `lines` (`{path: {line: [target]}}`) beside it, and returns it read back."""
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        head = f"# reach {rev or self.base} {dirty}\n"
        ix = lambda ts: " ".join(str(targets.index(t)) for t in ts)
        with open(os.path.join(d, "reach.tsv"), "w", encoding="utf-8") as f:
            f.write(f"{head}# targets {' '.join(targets)}\n# failed {' '.join(failed)}\n")
            f.writelines(f"{k}\t{ix(ts)}\n" for k, ts in rows.items())
        if lines is not None:
            with open(os.path.join(d, "reach-lines.tsv"), "w", encoding="utf-8") as f:
                f.write(f"{head}# macros mac when let\n")
                sets = [ts for ls in lines.values() for ts in ls.values()]
                f.writelines(f"s{k}\t{ix(ts)}\n" for k, ts in enumerate(sets))
                k = 0
                for p, ls in lines.items():
                    f.write(p + "\t" + " ".join(f"{n}:s{k + j}" for j, n in enumerate(ls)) + "\n")
                    k += len(ls)
        return po.Reach(os.path.join(d, "reach.tsv"))

    def owed(self, reach=None, head=None):
        return set(po.owed(self.base, reach, head)[0])


class Engine(Repo):
    ROWS = {"vaelii.impl.x/f": ["alpha"], "vaelii.impl.x/g": ["beta", "ab:genl-read"],
            "vaelii.impl.x": ["ab:starter-load"], "vaelii.impl.x/table-row": ["beta"]}

    def owed_by(self, old, new):
        self.change("src/vaelii/impl/x.clj", old, new)
        return self.owed(self.reach(self.ROWS))

    def test_a_defn_the_map_holds_owes_the_targets_that_executed_it(self):
        self.assertEqual(self.owed_by("(defn f [] 1)", "(defn f [] 10)"), {"alpha"})

    def test_a_defn_no_target_executes_owes_nothing_though_a_keyword_names_it(self):
        self.change("src/vaelii/impl/x.clj", "(defn dead [] 3)", "(defn dead [] 30)")
        sel, unreached = po.owed(self.base, self.reach(self.ROWS))
        self.assertEqual((set(sel), unreached), (set(), ["src/vaelii/impl/x.clj: vaelii.impl.x/dead"]))

    def test_a_namespace_the_map_holds_no_key_for_owes_the_per_file_rules(self):
        self.change("src/vaelii/impl/y.clj", "(right\n        a)", "(right a)")
        self.assertEqual(self.owed(self.reach(self.ROWS)), {"all", "ab:all"})

    def test_a_defn_a_def_initializer_names_owes_its_namespace(self):
        self.assertEqual(self.owed_by("(defn table-row [] 4)", "(defn table-row [] 40)"),
                         {"alpha", "beta", "ab:genl-read", "ab:starter-load"})

    def test_a_new_defn_owes_nothing_and_its_caller_owes_its_targets(self):
        self.assertEqual(self.owed_by("(defn dead [] 3)", "(defn dead [] 3)\n\n(defn h [] 6)"), set())
        self.assertEqual(self.owed_by("(defn f [] 1)", "(defn h [] 6)\n\n(defn f [] (h))"), {"alpha"})

    def test_a_new_defn_a_changed_file_names_at_the_base_owes_its_namespace(self):
        self.change("src/vaelii/impl/x.clj", "(defn f [] 1)", "(defn f [] (later))")
        FILES["src/vaelii/impl/x.clj"], old = po.read("src/vaelii/impl/x.clj"), ENGINE
        self.addCleanup(FILES.__setitem__, "src/vaelii/impl/x.clj", old)
        self.base = self.commit()
        self.assertEqual(self.owed_by("(defn dead [] 3)", "(defn dead [] 3)\n\n(defn later [] 0)"),
                         {"alpha", "beta", "ab:genl-read", "ab:starter-load"})

    def test_a_deleted_defn_no_changed_file_names_owes_nothing(self):
        self.assertEqual(self.owed_by("(defn f [] 1)\n", ""), set())

    def test_a_deleted_defn_a_changed_file_still_names_owes_its_targets(self):
        self.assertEqual(self.owed_by("(defn g [] 2)\n", ""), {"beta", "ab:genl-read"})

    def test_a_declare_names_no_defn_at_load(self):
        self.assertEqual(self.owed_by("(defn g [] 2)", "(defn g [] 20)"), {"beta", "ab:genl-read"})

    def test_a_form_moved_within_its_file_owes_nothing(self):
        self.assertEqual(self.owed_by("(defn f [] 1)\n\n(defn g [] 2)", "(defn g [] 2)\n\n(defn f [] 1)"),
                         set())

    def test_a_def_changed_only_in_its_docstring_owes_nothing(self):
        self.assertEqual(self.owed_by('"Read by f."', '"Read by f and g."'), set())

    def test_a_def_changed_in_its_value_owes_its_namespace(self):
        self.assertEqual(self.owed_by("  nil)", "  false)"),
                         {"alpha", "beta", "ab:genl-read", "ab:starter-load"})

    def test_a_defmethod_owes_the_targets_of_the_namespace_key(self):
        self.assertEqual(self.owed_by("[_] 5)", "[_] 50)"), {"ab:starter-load"})

    def test_an_ns_form_owes_nothing(self):
        self.assertEqual(self.owed_by("(ns vaelii.impl.x)", "(ns vaelii.impl.x\n  (:require [a.b :as c]))"),
                         set())

    def test_a_defmacro_owes_every_target(self):
        sel = self.owed_by("(defmacro m [x] x)", "(defmacro m [x] (do x))")
        self.assertEqual((po.kind(dict.fromkeys(sel), False), po.kind(dict.fromkeys(sel), True)),
                         ("all", "all"))

    def test_a_target_missing_from_the_map_or_failed_in_it_is_owed(self):
        self.change("src/vaelii/impl/x.clj", "(defn f [] 1)", "(defn f [] 10)")
        sel, _ = po.owed(self.base, self.reach({"vaelii.impl.x/f": ["alpha"]},
                                                targets=["alpha", "beta", "ab:genl-read"],
                                                failed=["beta"]))
        self.assertEqual(sel, {"alpha": "src/vaelii/impl/x.clj: vaelii.impl.x/f",
                               "ab:starter-load": "not in the reach map",
                               "beta": "its census run threw"})

    def test_a_change_outside_src_and_the_kb_owes_nothing(self):
        self.write("README.md", "changed\n")
        self.assertEqual(self.owed(self.reach(self.ROWS, failed=["beta"])), set())

    def test_a_committed_change_reads_through_head(self):
        self.change("src/vaelii/impl/x.clj", "(defn f [] 1)", "(defn f [] 10)")
        head = self.commit()
        self.write("src/vaelii/impl/x.clj", ENGINE)
        self.assertEqual(self.owed(self.reach(self.ROWS), head), {"alpha"})


class ByLine(Repo):
    Y = "src/vaelii/impl/y.clj"
    ALL3 = ["alpha", "beta", "ab:genl-read"]
    LINES = {Y: {3: ALL3, 6: ALL3, 7: ALL3, 8: ["alpha", "beta"], 9: ["alpha"], 10: ["alpha"],
                 11: ["ab:genl-read"], 14: ["beta"], 15: ["beta"]}}
    ROWS = {"vaelii.impl.y/k": ALL3, "vaelii.impl.y/n": ["alpha", "beta"]}

    def owed_by(self, old, new, **kw):
        self.change(self.Y, old, new)
        return self.owed(self.reach(self.ROWS, lines=kw.pop("lines", self.LINES), **kw))

    def test_a_changed_call_owes_the_targets_that_executed_its_line(self):
        self.assertEqual(self.owed_by("(left a)", "(left (inc a))"), {"alpha"})

    def test_a_changed_argument_owes_the_targets_of_the_call_holding_it(self):
        self.assertEqual(self.owed_by("(right\n        a)", "(right\n        b)"), {"ab:genl-read"})

    def test_a_form_added_to_a_body_owes_the_targets_of_the_form_before_it(self):
        self.assertEqual(self.owed_by("(left a)\n", "(left a)\n        (extra a)\n"), {"alpha"})

    def test_a_binding_added_to_a_let_owes_the_targets_of_the_value_before_it(self):
        self.assertEqual(self.owed_by("[a (pre x)]", "[a (pre x) b (post a)]"), set(self.ALL3))

    def test_a_changed_test_owes_every_target_reaching_it(self):
        self.assertEqual(self.owed_by("(ok? a)", "(ok? x)"), {"alpha", "beta"})

    def test_a_docstring_comment_or_layout_change_owes_nothing(self):
        self.assertEqual(self.owed_by('"doc"', '"docs"'), set())
        self.assertEqual(self.owed_by("(more a))", "(more a)) ; c"), set())
        self.assertEqual(self.owed_by("(left a)", "(left  a)"), set())

    def test_a_wrapper_closing_in_a_run_of_closes_owes_the_targets_of_its_open(self):
        self.assertEqual(self.owed_by("(more a))", "(when (go? a) (more a)))"), {"alpha"})

    def test_a_moved_close_bracket_owes_the_lists_around_both_its_positions(self):
        self.assertEqual(self.owed_by("(left a)\n        (more a))", "(left a\n        (more a)))"),
                         set(self.ALL3))

    def test_a_change_in_a_macro_call_owes_the_targets_of_an_entry_list_around_it(self):
        self.assertEqual(self.owed_by("(mac (left x)", "(mac (left y)"), {"beta"})
        self.assertEqual(self.owed_by("       x))", "       y))"), {"alpha", "beta"})

    def test_a_change_no_entry_list_around_it_owes_the_targets_of_the_defn(self):
        self.assertEqual(self.owed_by("[x]\n  (let", "[y]\n  (let"), set(self.ALL3))

    def test_a_line_of_the_base_reads_the_map_through_the_diff_since_the_map(self):
        rev = self.base
        self.change(self.Y, "(ns vaelii.impl.y)", "(ns vaelii.impl.y)\n\n(defn z [] 1)\n")
        FILES[self.Y], old = po.read(self.Y), FILES[self.Y]
        self.addCleanup(FILES.__setitem__, self.Y, old)
        self.base = self.commit()
        self.assertEqual(self.owed_by("(left a)", "(left (inc a))", rev=rev), {"alpha"})

    def test_a_line_changed_since_the_map_owes_the_targets_of_the_list_around_it(self):
        rev = self.base
        self.change(self.Y, "(left a)", "(left2 a)")
        FILES[self.Y], old = po.read(self.Y), FILES[self.Y]
        self.addCleanup(FILES.__setitem__, self.Y, old)
        self.base = self.commit()
        self.assertEqual(self.owed_by("(left2 a)", "(left3 a)", rev=rev), {"alpha", "beta"})

    def test_a_map_measured_over_a_dirty_tree_reads_no_line(self):
        self.assertEqual(self.owed_by("(left a)", "(left (inc a))", dirty="2"), set(self.ALL3))


class Harnesses(Repo):
    def test_an_edited_check_entry_owes_that_check(self):
        self.change(po.PERF, ":run (fn [n] (helper n))", ":run (fn [n] (helper (inc n)))")
        self.assertEqual(self.owed(), {"alpha"})

    def test_a_comment_above_an_entry_belongs_to_the_entry_below_it(self):
        self.change(po.PERF, ";; beta's comment", ";; beta's comment, reworded")
        self.assertEqual(self.owed(), {"beta"})

    def test_a_line_deleted_from_an_entry_owes_that_check(self):
        self.change(po.PERF, "    :sizes [1 2]\n", "")
        self.assertEqual(self.owed(), {"alpha"})

    def test_a_helper_owes_the_checks_whose_entry_reaches_it(self):
        self.change(po.PERF, "(inc n)", "(+ n 1)")
        self.assertEqual(self.owed(), {"alpha"})

    def test_a_name_inside_a_string_is_no_edge(self):
        self.change(po.PERF, "(defn- spare [n] n)", "(defn- spare [n] (inc n))")
        self.assertEqual(self.owed(), {"alpha", "beta"})

    def test_a_form_no_entry_reaches_owes_every_check(self):
        self.change(po.PERF, "(run! :run checks)", "(run! :run (reverse checks))")
        self.assertEqual(self.owed(), {"alpha", "beta"})

    def test_a_probe_added_to_the_list_owes_that_probe(self):
        text = edit(AB, "(defn genl-read [] (fresh))",
                    "(defn genl-read [] (fresh))\n\n(defn arith [] (fresh))")
        self.write(po.AB, edit(text, "  [#'genl-read\n", "  [#'genl-read\n   #'arith\n"))
        self.assertEqual(self.owed(), {"ab:arith"})

    def test_a_shared_probe_helper_owes_every_probe_reaching_it(self):
        self.change(po.AB, "(defn- fresh [] 1)", "(defn- fresh [] 2)")
        self.assertEqual(self.owed(), {"ab:genl-read", "ab:starter-load"})

    def test_shipped_kb_content_owes_the_targets_reaching_a_loader(self):
        self.write("resources/kb/upper/a.txt", "(genl dog mammal)\n")
        self.assertEqual(self.owed(), {"beta", "ab:starter-load"})

    def test_a_loader_file_with_no_map_owes_the_targets_reaching_a_loader(self):
        for p in ("src/vaelii/host/seed.clj", "src/vaelii/starter.clj"):
            self.write(p, "(ns x)\n")
            self.base = self.commit()
            self.write(p, "(ns x)\n(def y 1)\n")
            self.assertEqual(self.owed(), {"beta", "ab:starter-load"}, p)
            self.assertEqual(self.owed(self.reach({po.ns_of(p): []})), set(), p)


class Fallback(unittest.TestCase):
    def test_an_impl_file_owes_its_groups(self):
        self.assertEqual(po.static_select("src/vaelii/impl/except.clj")[0], {"exceptions", "placement"})

    def test_an_engine_file_no_group_names_owes_every_check(self):
        for p in ("src/vaelii/impl/jtms.clj", "src/vaelii/impl/network_regions.clj", "src/vaelii/core.clj"):
            self.assertEqual(po.static_select(p)[0], {"all"}, p)

    def test_an_engine_file_owes_every_probe(self):
        for p in ("src/vaelii/core.clj", "src/vaelii/impl/kb.clj", "src/vaelii/impl/network_regions.clj"):
            self.assertEqual(po.static_select(p)[1], {"all"}, p)
        self.assertEqual(po.static_select("src/vaelii/host/cli.clj"), (set(), set()))

    def test_every_probe_is_one_line_beside_a_named_probe(self):
        self.assertEqual(po.kind({"ab:all": "a", "ab:starter-load": "b", "beta": "c"}, True), "all")
        self.assertEqual(po.kind({"ab:all": "a", "beta": "c"}, False), "beta")


class Parsing(unittest.TestCase):
    def test_forms_read_the_head_and_the_name_past_metadata(self):
        text = "(ns a)\n(defn- ^:private ^{:k 1} f\n  [])\n;; c\n(def ^long n 1)"
        self.assertEqual(po.forms(text), [(1, 1, "ns", "a"), (2, 4, "defn-", "f"),
                                          (5, 5, "def", "n")])

    def test_changed_lines_read_both_sides_of_each_hunk(self):
        diff = "@@ -3 +3 @@\n-a\n+b\n@@ -10,2 +9,0 @@\n@@ -20,0 +18,3 @@"
        self.assertEqual(po.changed_lines(diff), ({3, 10, 11}, {3, 18, 19, 20}))

    def test_symbols_drop_strings_comments_and_keywords(self):
        self.assertEqual(po.symbols('(g {:f 1 ::h 2 :a/b 3} "k l" ; m\n x/y)'), {"g", "x", "y"})

    def test_a_tree_reads_quoted_lists_and_case_tests_as_data(self):
        t = po.Tree("(f '(g x) (case k (:a :b) (h) 2) ^String y #_(z))")
        f = t.root.children[0]
        quoted, case = f.children[1], f.children[2]
        self.assertEqual((quoted.data, case.children[2].data, case.children[3].data),
                         (True, True, False))
        self.assertEqual(f.items(t), ["f", quoted, case, "y"])

    def test_sites_read_a_token_change_and_an_insertion(self):
        old, new = po.Tree("(f a\n   b)"), po.Tree("(f c\n   b\n   d)")
        diff = "@@ -1 +1 @@\n@@ -2 +2,2 @@"
        self.assertEqual(po.sites(old, new, diff), [(2, False), (4, True)])

    def test_line_map_follows_each_hunk(self):
        f = po.line_map("@@ -2,0 +3,2 @@\n@@ -5 +7 @@")
        self.assertEqual([f(n) for n in (1, 3, 5, 6, 7, 8)], [1, None, 3, 4, None, 6])

    def test_ns_of_demunges_the_path(self):
        self.assertEqual(po.ns_of("src/vaelii/impl/decide/dense_kv.clj"), "vaelii.impl.decide.dense-kv")


if __name__ == "__main__":
    unittest.main()
