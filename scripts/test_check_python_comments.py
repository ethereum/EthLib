"""Tests of `check_python_comments.py` on planted Python text and on a small git repository."""

import contextlib
import importlib.util
import io
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location(
    "check_python_comments", HERE / "check_python_comments.py"
)
assert spec and spec.loader
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

MESSAGE = "sentence runs onto this line; give each sentence a line of its own"


def wraps(text: str, changed: set[int] | None = None) -> list[int]:
    return [finding.line for finding in check.check_text("t.py", text, changed)]


class WrappedSentences(unittest.TestCase):
    def test_the_example_of_the_rule(self):
        # The comment of #1226 that the rule was written for.
        text = (
            "# The two proofs below are one leaf each, built by hand so that the value under the\n"
            "# key is not what the check reads. The leaf of an address is the list of 0x20\n"
            "# followed by the hash of the address.\n"
        )
        self.assertEqual(wraps(text), [2, 3])

    def test_one_sentence_per_line(self):
        text = "# One sentence.\n# Another one?\n#\n# A label:\n# Its value!\nx = 1\n"
        self.assertEqual(wraps(text), [])

    def test_sentence_end_before_a_closer(self):
        self.assertEqual(wraps("# One (`a.`)\n# Two.\n"), [])
        self.assertEqual(wraps("# One (a)\n# two.\n"), [2])

    def test_run_on_after_a_colon(self):
        self.assertEqual(wraps("# The bytes it shares:\n# h, then m.\n"), [2])
        # A capital, a list item, a URL or code after the colon starts something new.
        text = (
            "# A label:\n"
            "# A new sentence.\n"
            "# The items:\n"
            "# - one\n"
            "#\n"
            "# The source:\n"
            "# https://example.org/a\n"
            "# Usage:\n"
            "#\n"
            "#     uv run a.py\n"
        )
        self.assertEqual(wraps(text), [])

    def test_list_items(self):
        self.assertEqual(wraps("# A list:\n# - one\n# - two\n# 1. three\n"), [])
        # The continuation of an item is a wrapped sentence too.
        self.assertEqual(wraps("# - an item that\n#   wraps.\n"), [2])

    def test_provenance_records(self):
        text = (
            "# The vectors of a file.\n"
            "#\n"
            "# File: a/b.json\n"
            "# Files: c.json, d.json\n"
            "# File sha256: 0123abcd (G1)\n"
            "# Repository: owner/repo\n"
            "# Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9\n"
            "# Licence: Apache 2.0 (LICENSE)\n"
            "# SPDX-License-Identifier: Apache-2.0\n"
            "# Adapted from another project.\n"
        )
        self.assertEqual(wraps(text), [])
        # A label that is not a field of a record starts a sentence like any other.
        self.assertEqual(wraps("# Why: the value is\n# the least.\n"), [2])

    def test_blocks_that_are_not_prose(self):
        text = (
            "# Run it as\n"
            "#\n"
            "#     uv run python a.py --check\n"
            "#     uv run python a.py --output b\n"
            "#\n"
            "# ```text\n"
            "# a fenced block, whose lines\n"
            "# wrap freely\n"
            "# ```\n"
            "# | a | table |\n"
            "# | row | b |\n"
            "# ## A heading\n"
            "# https://example.org/a/link\n"
            "# ---\n"
        )
        self.assertEqual(wraps(text), [])
        self.assertEqual(wraps("#!/usr/bin/env python3\n# A script.\n"), [])

    def test_runs_of_comments(self):
        # A blank line, a line of code or another column ends a run.
        self.assertEqual(wraps("# One\n\n# two.\n"), [])
        self.assertEqual(wraps("# One\nx = 1\n# two.\n"), [])
        self.assertEqual(wraps("if x:\n    # One\n# two.\n    pass\n"), [])
        # A comment after code is a comment of its own.
        self.assertEqual(wraps("x = 1  # one\n# two.\n"), [])
        self.assertEqual(wraps("def f():\n    # One\n    # two.\n    pass\n"), [3])

    def test_strings_are_not_comments(self):
        self.assertEqual(wraps('x = """\n# One\n# two.\n"""\n'), [])

    def test_only_changed_pairs(self):
        text = "# One\n# two\n# three.\n"
        self.assertEqual(wraps(text, {1}), [2])
        self.assertEqual(wraps(text, {3}), [3])
        self.assertEqual(wraps(text, set()), [])


class Modes(unittest.TestCase):
    def git(self, root: Path, *args: str) -> None:
        config = ["-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run(["git", *config, *args], cwd=root, check=True, capture_output=True)

    def run_main(self, root: Path, *args: str) -> tuple[int, str]:
        out = io.StringIO()
        with mock.patch.object(check, "ROOT", root), contextlib.redirect_stdout(out):
            status = check.main(["check_python_comments.py", *args])
        return status, out.getvalue()

    def test_branch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.git(root, "init", "-q", "-b", "base")
            old = "# One\n# two.\nx = 1\n"
            (root / "old.py").write_text(old)
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "base")
            self.git(root, "checkout", "-q", "-b", "topic")
            (root / "old.py").write_text(old + "# Three\n# four.\n")
            (root / "new.py").write_text("# One\n# two.\n")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "topic")
            # A new file that is not added: `git diff` alone does not list it.
            (root / "untracked.py").write_text("# One\n# two.\n")

            with mock.patch.object(check, "ROOT", root):
                self.assertEqual(
                    check.changed_lines("base"),
                    {"new.py": {1, 2}, "old.py": {4, 5}, "untracked.py": {1, 2}},
                )
            status, out = self.run_main(root, "--base", "base")
            self.assertEqual(status, 1)
            self.assertEqual(
                out.splitlines(),
                [
                    f"new.py:2: {MESSAGE}",
                    f"old.py:5: {MESSAGE}",
                    f"untracked.py:2: {MESSAGE}",
                    "3 wrapped comment line(s).",
                ],
            )

    def test_all_tracked_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.git(root, "init", "-q", "-b", "base")
            (root / "old.py").write_text("# One\n# two.\n")
            (root / "fine.py").write_text("# One.\n# Two.\n")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "base")
            (root / "untracked.py").write_text("# One\n# two.\n")

            status, out = self.run_main(root, "--all", "--github")
            self.assertEqual(status, 1)
            self.assertEqual(
                out.splitlines(),
                [
                    f"::error file=old.py,line=2,title=Python comment::{MESSAGE}",
                    "1 wrapped comment line(s).",
                ],
            )
            (root / "old.py").write_text("# One.\n# Two.\n")
            self.assertEqual(self.run_main(root, "--all"), (0, "No wrapped comment lines.\n"))


if __name__ == "__main__":
    unittest.main()
