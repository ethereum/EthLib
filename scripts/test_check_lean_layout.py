"""
Check `check_lean_layout.py` itself, on planted Lean text and on a small git repository.

    uv run --no-project --python 3.12 python -m unittest scripts/test_check_lean_layout.py

Only the standard library is used, like the script.
"""
import contextlib
import importlib.util
import io
import subprocess
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_lean_layout", HERE / "check_lean_layout.py")
layout = importlib.util.module_from_spec(spec)
spec.loader.exec_module(layout)

URL = "https://example.org/" + "a" * 120


def lines_of(text: str, changed: set[int] | None = None) -> list[int]:
    return [f.line for f in layout.check_text("T.lean", text, changed)]


def pairs(text: str, changed: set[int] | None = None) -> list[int]:
    return [f.line for f in layout.check_text("T.lean", text, changed)
            if "sentence lines" in f.message]


class LineLength(unittest.TestCase):
    def test_limit(self):
        self.assertEqual(lines_of("x" * 100), [])
        self.assertEqual(lines_of("x" * 101), [1])

    def test_counts_characters_not_bytes(self):
        self.assertEqual(lines_of("α" * 100), [])
        self.assertEqual(lines_of("α" * 101), [1])

    def test_only_changed_lines(self):
        text = "x" * 101 + "\n" + "y" * 101
        self.assertEqual(lines_of(text, {2}), [2])
        self.assertEqual(lines_of(text, set()), [])

    def test_url_alone(self):
        for line in (URL, "  " + URL, "-- " + URL, "/-- " + URL + " -/", "/-! " + URL,
                     "<" + URL + ">", "[draft]: " + URL):
            with self.subTest(line=line):
                self.assertEqual(lines_of(line), [])

    def test_url_in_a_sentence(self):
        self.assertEqual(lines_of(f"-- See [the draft]({URL}).", {1}), [1])
        self.assertEqual(lines_of(f"def x := \"{URL}\"", {1}), [1])


class CommentLayout(unittest.TestCase):
    def test_touching_sentences(self):
        self.assertEqual(pairs("/-- One.\nTwo.\nThree. -/\ndef x := 1"), [2, 3])
        self.assertEqual(pairs("/-!\n# Title\n\nOne.\nTwo.\n-/"), [5])

    def test_separated_sentences(self):
        self.assertEqual(pairs("/-- One.\n\nTwo. -/\ndef x := 1"), [])
        self.assertEqual(pairs("/-!\n# Title\nOne.\n\nTwo.\n-/"), [])

    def test_lists_tables_and_links(self):
        text = ("/-!\nThe rules:\n- one\n- two,\n  continued\n1. three\n\n| a | b |\n| c | d |\n\n"
                f"See the draft.\n[draft]: {URL}\n{URL}\n-/")
        self.assertEqual(pairs(text), [])

    def test_code_blocks(self):
        fenced = "/-!\nText.\n\n```\nlet a := 1\nlet b := 2\n```\n-/"
        indented = "/-!\nText.\n\n    let a := 1\n    let b := 2\n-/"
        self.assertEqual(pairs(fenced), [])
        self.assertEqual(pairs(indented), [])

    def test_line_comments(self):
        self.assertEqual(pairs("-- One.\n-- Two.\ndef x := 1"), [2])
        self.assertEqual(pairs("-- One.\n--\n-- Two.\ndef x := 1"), [])
        self.assertEqual(pairs("  -- One.\n  -- Two.\ndef x := 1"), [2])

    def test_line_comments_apart(self):
        self.assertEqual(pairs("def x := 1 -- One.\n-- Two.\ndef y := 2"), [])
        self.assertEqual(pairs("-- One.\ndef x := 1\n-- Two."), [])
        self.assertEqual(pairs("-- One.\n\n-- Two."), [])

    def test_decorative_line(self):
        self.assertEqual(pairs("-- One.\n-- ------"), [])

    def test_nested_block_comment(self):
        self.assertEqual(pairs("/- One. /- inner -/\nTwo. -/"), [2])

    def test_strings_and_characters(self):
        self.assertEqual(pairs('def s := "-- One.\n-- Two."'), [])
        self.assertEqual(pairs("def s := r#\"/- One.\nTwo. -/\"#"), [])
        self.assertEqual(pairs("def c := '\"'\n-- One.\n-- Two."), [3])
        self.assertEqual(pairs("def x' := 1\n-- One.\n-- Two."), [3])

    def test_only_changed_pairs(self):
        text = "/-- One.\nTwo.\n\nThree.\nFour. -/\ndef x := 1"
        self.assertEqual(pairs(text, {4}), [5])
        self.assertEqual(pairs(text, {5}), [5])
        self.assertEqual(pairs(text, {3, 6}), [])


class ChangedLines(unittest.TestCase):
    def git(self, root: Path, *args: str) -> None:
        config = ["-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run(["git", *config, *args], cwd=root, check=True, capture_output=True)

    def test_branch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.git(root, "init", "-q", "-b", "base")
            old = "x" * 101 + "\n/-- One.\nTwo. -/\ndef x := 1\n"
            (root / "Old.lean").write_text(old)
            (root / "Doc.md").write_text("y" * 101 + "\n")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "base")
            self.git(root, "checkout", "-q", "-b", "topic")
            (root / "Old.lean").write_text(old + "-- Three.\n")
            (root / "New.lean").write_text("-- One.\n-- Two.\n")
            (root / "Doc.md").write_text("y" * 102 + "\n")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "topic")

            saved = layout.ROOT
            layout.ROOT = root
            try:
                self.assertEqual(layout.changed_lines("base"),
                                 {"New.lean": {1, 2}, "Old.lean": {5}})
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    status = layout.main(["check_lean_layout.py", "--base", "base"])
            finally:
                layout.ROOT = saved
            self.assertEqual(status, 1)
            self.assertIn("New.lean:2:", out.getvalue())
            self.assertNotIn("Old.lean", out.getvalue())


if __name__ == "__main__":
    unittest.main()
