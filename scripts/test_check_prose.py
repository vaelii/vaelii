#!/usr/bin/env python3
"""Tests of check-prose.py: P7's prose-unit reader, sentence splitter and word counter,
and the per-file budget. Run: python3 scripts/test_check_prose.py"""

import contextlib
import importlib.util
import io
import os
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("check_prose", os.path.join(HERE, "check-prose.py"))
cp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cp)


def words(n):
    """Returns `n` plain words, the first capitalised so that it can start a sentence."""
    return " ".join(f"{'W' if i == 0 else 'w'}{i}" for i in range(n))


def counts(rel, text):
    """Returns the word count of every sentence `rel`'s P7 reader finds in `text`."""
    return [n for unit in cp.prose_units(rel, text.split("\n"))
            for _, n, _ in cp.sentences(unit)]


def quietly(fn, *args):
    """Returns `fn(*args)` and what it printed."""
    with contextlib.redirect_stdout(io.StringIO()) as out:
        return fn(*args), out.getvalue()


class Units(unittest.TestCase):
    def test_each_list_item_is_its_own_unit(self):
        text = f"- {words(25)}\n- {words(25)}\n  {words(5)}\n* {words(3)}\n1. {words(4)}"
        self.assertEqual(counts("a.md", text), [25, 30, 3, 4])

    def test_the_covers_not_here_assumes_bullets_are_three_units(self):
        text = (f"- **Covers:** {words(20)}\n  {words(20)}\n"
                f"- **Not here:** {words(30)}\n"
                f"- **Assumes:** {words(10)}")
        self.assertEqual(counts("a.md", text), [40, 30, 10])

    def test_a_blank_line_ends_a_paragraph(self):
        self.assertEqual(counts("a.md", f"{words(30)}\n\n{words(30)}"), [30, 30])

    def test_fences_tables_headings_html_and_rules_belong_to_no_unit(self):
        text = "\n".join([
            "# A heading of six words here", f"```clojure", f"{words(50)}", "```",
            f"| {words(50)} |", f"<details><summary>{words(50)}</summary>",
            "<!--", f"{words(50)}", "-->", "---", f"{words(7)}."])
        self.assertEqual(counts("a.md", text), [7])

    def test_a_blockquote_line_is_prose(self):
        self.assertEqual(counts("a.md", f"> {words(5)}.\n> {words(6)}."), [5, 6])


class Splitter(unittest.TestCase):
    def test_a_bold_run_in_label_is_not_a_sentence(self):
        self.assertEqual(counts("a.md", f"**An open.** {words(10)}."), [10])
        self.assertEqual(counts("a.md", f"- *Migration:* {words(10)}."), [10])

    def test_a_bold_subject_is_part_of_its_sentence(self):
        self.assertEqual(counts("a.md", f"**The check** {words(8)}."), [10])

    def test_abbreviations_end_no_sentence(self):
        for abbr in ("e.g.", "i.e.", "vs.", "cf.", "E.g."):
            with self.subTest(abbr=abbr):
                self.assertEqual(counts("a.md", f"{words(3)} {abbr} Foo {words(3)}."), [8])

    def test_decimals_versions_and_file_names_end_no_sentence(self):
        for token in ("1.5", "0.33.0", "seal.nippy", "docs/api.md"):
            with self.subTest(token=token):
                self.assertEqual(counts("a.md", f"{words(3)} {token} {words(3)}."), [7])

    def test_a_period_inside_backticks_ends_no_sentence(self):
        self.assertEqual(counts("a.md", f"{words(3)} `a. B` {words(3)}."), [7])

    def test_a_sentence_ends_before_a_capital_a_backtick_or_a_digit(self):
        text = f"{words(3)}. Next {words(2)}. `x` {words(2)}? 4 {words(2)}! (b) c."
        self.assertEqual(counts("a.md", text), [3, 3, 3, 3, 2])

    def test_a_period_before_a_lowercase_word_ends_no_sentence(self):
        self.assertEqual(counts("a.md", f"{words(3)} etc. and {words(3)}."), [8])

    def test_closing_marks_after_the_period_stay_with_the_sentence(self):
        self.assertEqual(counts("a.md", f"({words(3)}.) {words(4)}. \"{words(2)}.\" B c."),
                         [3, 4, 2, 2])


class Counter(unittest.TestCase):
    def test_a_backtick_span_is_one_word(self):
        self.assertEqual(counts("a.md", "Call `v/ask` with `{:recover? false}` now."), [5])

    def test_a_link_counts_its_text_only(self):
        self.assertEqual(counts("a.md", "See [the API page](docs/api.md#ask-a-kb) here."), [5])
        self.assertEqual(counts("a.md", "See [the API page][api] here."), [5])

    def test_punctuation_alone_is_no_word(self):
        self.assertEqual(counts("a.md", "One — two -> three | four."), [4])

    def test_a_sentence_reports_the_line_its_first_word_is_on(self):
        unit = cp.md_units(enumerate([f"{words(3)}. Second", f"{words(3)}."], 1))[0]
        self.assertEqual([ln for ln, _, _ in cp.sentences(unit)], [1, 1])
        unit = cp.md_units(enumerate([f"{words(3)}.", f"Second {words(3)}."], 1))[0]
        self.assertEqual([ln for ln, _, _ in cp.sentences(unit)], [1, 2])


class CodeProse(unittest.TestCase):
    def test_a_clojure_comment_wrapped_across_lines_is_one_sentence(self):
        text = f";; {words(20)}\n;; {words(20)}.\n(defn f [] 1)"
        self.assertEqual(counts("a.clj", text), [40])

    def test_a_comment_after_code_on_its_line_is_not_read(self):
        self.assertEqual(counts("a.clj", f"(f) ; {words(50)}\n;; {words(3)}."), [3])

    def test_a_docstring_wrapped_across_lines_is_one_sentence(self):
        text = f'(defn f\n  "{words(20)}\n  {words(20)}."\n  [] "not a docstring {words(50)}")'
        self.assertEqual(counts("a.clj", text), [40])

    def test_a_docstring_opening_with_a_verb_is_split_and_counted(self):
        text = f'(defn f\n  "Answers {words(4)}. Returns {words(39)}\n  {words(1)}."\n  [])'
        self.assertEqual(counts("a.clj", text), [5, 41])

    def test_a_string_value_of_a_def_is_not_a_docstring(self):
        self.assertEqual(counts("a.clj", f'(def x "{words(50)}")'), [])

    def test_a_hash_comment_wrapped_across_lines_is_one_sentence(self):
        for rel in ("a.py", "a.sh"):
            with self.subTest(rel=rel):
                text = f"#!/bin/sh\n# {words(20)}\n#   {words(20)}.\nx = 1"
                self.assertEqual(counts(rel, text), [40])

    def test_an_aligned_row_belongs_to_no_unit_and_a_dedent_starts_one(self):
        text = (f'(defn f\n  "{words(3)}:\n\n    :id     {words(30)}\n'
                f'            {words(4)}\n  {words(5)}."\n  [])')
        self.assertEqual(counts("a.clj", text), [3, 4, 5])

    def test_a_txt_or_edn_file_has_no_prose_units(self):
        self.assertEqual(counts("a.txt", words(50)), [])
        self.assertEqual(counts("a.edn", f";; {words(50)}"), [])


class Hits(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        self.saved = cp.ROOT
        cp.ROOT = self.root

    def tearDown(self):
        cp.ROOT = self.saved

    def write(self, rel, text):
        with open(os.path.join(self.root, rel), "w") as f:
            f.write(text)

    def p7(self, rel):
        return [(ln, text) for ln, code, text in cp.hits_in(rel) if code == "P7"]

    def test_a_sentence_of_max_words_is_a_hit_and_one_word_fewer_is_not(self):
        self.write("a.md", f"{words(cp.MAX_WORDS)}.\n\n{words(cp.MAX_WORDS - 1)}.")
        self.assertEqual([ln for ln, _ in self.p7("a.md")], [1])

    def test_a_hit_prints_its_count_and_first_twelve_words(self):
        self.write("a.md", f"Intro.\n{words(cp.MAX_WORDS)}.")
        (ln, text), = self.p7("a.md")
        self.assertEqual(cp.fmt("a.md", ln, "P7", text),
                         f"a.md:2: P7 ({cp.MAX_WORDS} words) {words(12)}…")

    def test_changelog_released_sections_are_not_read(self):
        self.write("CHANGELOG.md", f"## Unreleased\n\n{words(50)}.\n\n## 0.1.0\n\n{words(50)}.")
        self.assertEqual([ln for ln, _ in self.p7("CHANGELOG.md")], [3])

    def test_exempt_files_are_not_scanned(self):
        cp.ROOT = self.saved
        self.assertFalse(set(cp.EXEMPT) & set(cp.scan_files()))


class Budget(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.path = os.path.join(self.dir, "budget.txt")
        with open(self.path, "w") as f:
            f.write("# header\n3\ta.md\tawaiting rewrite\n")

    def detail(self, n):
        return {"a.md": [(i, "P1", "x") for i in range(n)]} if n else {}

    def test_update_lowers_a_count_and_never_raises_one(self):
        self.assertEqual(quietly(cp.update, "p", self.path, "", {"a.md": 2})[0], 0)
        self.assertEqual(cp.read_baseline(self.path)[0], {"a.md": 2})
        self.assertEqual(quietly(cp.update, "p", self.path, "", {"a.md": 5})[0], 1)
        self.assertEqual(cp.read_baseline(self.path)[0], {"a.md": 2})

    def test_update_never_adds_a_file_the_budget_does_not_list(self):
        rc, out = quietly(cp.update, "p", self.path, "", {"a.md": 3, "b.md": 4})
        self.assertEqual(rc, 1)
        self.assertEqual(cp.read_baseline(self.path)[0], {"a.md": 3})
        self.assertIn("b.md: budget 0, found 4", out)

    def test_update_drops_a_file_whose_hits_are_gone(self):
        self.assertEqual(quietly(cp.update, "p", self.path, "", {})[0], 0)
        self.assertEqual(cp.read_baseline(self.path)[0], {})

    def test_seed_writes_an_absent_budget_file_and_leaves_an_existing_one(self):
        fresh = os.path.join(self.dir, "fresh.txt")
        self.assertEqual(quietly(cp.seed, "p", fresh, "", {"a.md": 4, "b.md": 1})[0], 0)
        self.assertEqual(cp.read_baseline(fresh)[0], {"a.md": 4, "b.md": 1})
        self.assertEqual(quietly(cp.seed, "p", self.path, "", {"a.md": 9})[0], 0)
        self.assertEqual(cp.read_baseline(self.path)[0], {"a.md": 3})

    def test_check_fails_over_and_under_budget_and_passes_at_it(self):
        self.assertEqual(quietly(cp.check, "p", self.path, "m", self.detail(4))[0], 1)
        self.assertEqual(quietly(cp.check, "p", self.path, "m", self.detail(2))[0], 1)
        rc, out = quietly(cp.check, "prose", self.path, "m", self.detail(3))
        self.assertEqual((rc, out), (0, "prose: 3 of 3 allowed, 1 files remaining\n"))

    def test_the_summary_labels_are_the_ones_lint_reads(self):
        self.assertEqual([ledger[0] for ledger in cp.LEDGERS], ["prose", "prose P7"])

    def test_check_holds_a_file_absent_from_the_budget_at_zero(self):
        rc, out = quietly(cp.check, "p", self.path, "m",
                          {**self.detail(3), "b.md": [(1, "P1", "x")]})
        self.assertEqual(rc, 1)
        self.assertIn("b.md: 1 hits, budget 0", out)


if __name__ == "__main__":
    unittest.main()
