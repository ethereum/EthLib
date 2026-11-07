"""Tests of `check_lean_layout.py` on planted Lean text and on a small git repository."""

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
spec = importlib.util.spec_from_file_location("check_lean_layout", HERE / "check_lean_layout.py")
assert spec and spec.loader
layout = importlib.util.module_from_spec(spec)
spec.loader.exec_module(layout)

URL = "https://example.org/" + "a" * 120


def lines_of(text: str, changed: set[int] | None = None) -> list[int]:
    return [f.line for f in layout.check_text("T.lean", text, changed)]


def pairs(text: str, changed: set[int] | None = None) -> list[int]:
    return [
        f.line for f in layout.check_text("T.lean", text, changed) if "sentence lines" in f.message
    ]


def wraps(text: str, changed: set[int] | None = None) -> list[int]:
    return [f.line for f in layout.check_text("T.lean", text, changed) if "runs onto" in f.message]


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
        for line in (
            URL,
            "  " + URL,
            "-- " + URL,
            "/-- " + URL + " -/",
            "/-! " + URL,
            "<" + URL + ">",
            "[draft]: " + URL,
        ):
            with self.subTest(line=line):
                self.assertEqual(lines_of(line), [])

    def test_url_in_a_sentence(self):
        self.assertEqual(lines_of(f"-- See [the draft]({URL}).", {1}), [1])
        self.assertEqual(lines_of(f'def x := "{URL}"', {1}), [1])


class CommentLayout(unittest.TestCase):
    def test_touching_sentences(self):
        self.assertEqual(pairs("/-- One.\nTwo.\nThree. -/\ndef x := 1"), [2, 3])
        self.assertEqual(pairs("/-!\n# Title\n\nOne.\nTwo.\n-/"), [5])

    def test_separated_sentences(self):
        self.assertEqual(pairs("/-- One.\n\nTwo. -/\ndef x := 1"), [])
        self.assertEqual(pairs("/-!\n# Title\nOne.\n\nTwo.\n-/"), [])

    def test_lists_tables_and_links(self):
        text = (
            "/-!\nThe rules:\n- one\n- two,\n  continued\n1. three\n\n| a | b |\n| c | d |\n\n"
            f"See the draft.\n[draft]: {URL}\n{URL}\n-/"
        )
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
        self.assertEqual(lines_of("/- One. /- inner. -/\nTwo. -/"), [2])

    def test_strings_and_characters(self):
        self.assertEqual(pairs('def s := "-- One.\n-- Two."'), [])
        self.assertEqual(pairs('def s := r#"/- One.\nTwo. -/"#'), [])
        self.assertEqual(pairs("def c := '\"'\n-- One.\n-- Two."), [3])
        self.assertEqual(pairs("def x' := 1\n-- One.\n-- Two."), [3])

    def test_only_changed_pairs(self):
        text = "/-- One.\nTwo.\n\nThree.\nFour. -/\ndef x := 1"
        self.assertEqual(pairs(text, {4}), [5])
        self.assertEqual(pairs(text, {5}), [5])
        self.assertEqual(pairs(text, {3, 6}), [])


# The two wrapped sentences of the network fork identifier that the rule was written for.
FORK_ID_LINK = (
    "/-- The header of that block has the timestamp 0, as\n"
    "[`genesishashestest.json`](https://github.com/ethereum/tests/blob/c67e/genesishashestest.json)\n"
    "of the Ethereum tests holds it. -/\ndef x := 1"
)
FORK_ID_RULE = (
    "/-!\nEIP-6122 says that a node need not tell the two apart, but rule 1a must: it compares the"
    " next\nfork of a peer with the local head.\n-/"
)


WRAP_MESSAGE = "sentence runs onto this line; give each sentence a line of its own"


class WrappedSentences(unittest.TestCase):
    def test_fork_id_examples(self):
        self.assertEqual(wraps(FORK_ID_LINK), [2, 3])
        self.assertEqual(wraps(FORK_ID_RULE), [3])
        # The wrap is not also reported as two touching sentence lines.
        self.assertEqual(pairs(FORK_ID_RULE), [])

    def test_split_sentences_and_reference_links(self):
        split = (
            "/-!\nEIP-6122 says that a node need not tell the two apart.\n\n"
            "Rule 1a must, since it compares a peer's next fork with the local head.\n-/"
        )
        reference = (
            "/-- The header of that block has the timestamp 0, as [the file][genesis] holds it."
            f"\n\n[genesis]: {URL}\n[other]: {URL} -/\ndef x := 1"
        )
        self.assertEqual(wraps(split), [])
        self.assertEqual(wraps(reference), [])

    def test_sentence_end(self):
        for end in (".", "?", "!", ":", ".)", ".`", ".*", '."', ".]"):
            with self.subTest(end=end):
                self.assertEqual(wraps(f"/-- One{end}\nTwo. -/\ndef x := 1"), [])
        self.assertEqual(wraps("/-- One,\nTwo. -/\ndef x := 1"), [2])
        self.assertEqual(wraps("/-- One\nmore\nand more. -/\ndef x := 1"), [2, 3])

    def test_list_items(self):
        self.assertEqual(wraps("/-!\n- one\n- two,\n  continued.\n1. three\n-/"), [4])
        # Each sentence of an item on a line of its own is not a wrap.
        self.assertEqual(wraps("/-!\n- One.\n  Two.\n- Three.\n-/"), [])
        self.assertEqual(wraps("/-!\nThe rules\n- one\n- two\n-/"), [])

    def test_blocks_that_are_not_prose(self):
        fenced = "/-!\nText\n```\nlet a := 1\nlet b := 2\n```\nMore\n-/"
        indented = "/-!\nText\n\n    let a := 1\n    let b := 2\n-/"
        table = "/-!\n| a | b\n| c | d\n-/"
        heading = "/-!\n# Title\nText.\n-/"
        self.assertEqual(wraps(fenced), [])
        self.assertEqual(wraps(indented), [])
        self.assertEqual(wraps(table), [])
        self.assertEqual(wraps(heading), [])
        self.assertEqual(wraps("-- One\n-- ------"), [])

    def test_line_comments(self):
        self.assertEqual(wraps("  -- One sentence that\n  -- goes on.\ndef x := 1"), [2])
        self.assertEqual(wraps("def x := 1 -- One\n-- Two."), [])
        self.assertEqual(wraps('def s := "-- One\n-- Two."'), [])
        # An equation aligned under the line above is code, not a wrapped sentence.
        self.assertEqual(wraps("  -- a * v = b * v + c\n  --       = d\ndef x := 1"), [])

    def test_only_changed_pairs(self):
        text = "/-- One\ntwo.\n\nThree\nfour. -/\ndef x := 1"
        self.assertEqual(wraps(text, {1}), [2])
        self.assertEqual(wraps(text, {5}), [5])
        self.assertEqual(wraps(text, {3, 6}), [])

    def test_rules(self):
        text = "x" * 101 + "\n/-- One\ntwo.\nThree. -/\ndef x := 1"
        messages = [f.message for f in layout.check_text("T.lean", text, None, ("wrap",))]
        self.assertEqual(len(messages), 1)
        self.assertIn("runs onto", messages[0])
        self.assertEqual(len(layout.check_text("T.lean", text, None, ("length",))), 1)
        self.assertEqual(len(layout.check_text("T.lean", text, None)), 3)


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

            with mock.patch.object(layout, "ROOT", root):
                self.assertEqual(
                    layout.changed_lines("base"), {"New.lean": {1, 2}, "Old.lean": {5}}
                )
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    status = layout.main(["check_lean_layout.py", "--base", "base"])
            self.assertEqual(status, 1)
            self.assertIn("New.lean:2:", out.getvalue())
            self.assertNotIn("Old.lean", out.getvalue())

    def test_untracked_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.git(root, "init", "-q", "-b", "base")
            (root / "Old.lean").write_text("def x := 1\n")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "base")
            # A new file that is not added: `git diff` alone does not list it.
            (root / "New.lean").write_text("-- One.\n-- Two.\n" + "z" * 101 + "\n")
            (root / "Ignored.lean").write_text("w" * 101 + "\n")
            (root / ".gitignore").write_text("Ignored.lean\n")

            with mock.patch.object(layout, "ROOT", root):
                self.assertEqual(layout.changed_lines("base"), {"New.lean": {1, 2, 3}})
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    status = layout.main(["check_lean_layout.py", "--base", "base"])
            self.assertEqual(status, 1)
            self.assertIn("New.lean:2:", out.getvalue())
            self.assertIn("New.lean:3:", out.getvalue())
            self.assertNotIn("Ignored.lean", out.getvalue())

    def test_all_tracked_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.git(root, "init", "-q", "-b", "base")
            (root / "Old.lean").write_text("-- One\n-- two.\n" + "x" * 101 + "\n")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "base")
            (root / "Untracked.lean").write_text("-- One\n-- two.\n")

            with mock.patch.object(layout, "ROOT", root):
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    status = layout.main(["check_lean_layout.py", "--all", "--rule", "wrap"])
            self.assertEqual(status, 1)
            self.assertEqual(
                out.getvalue().splitlines(),
                [f"Old.lean:2: {WRAP_MESSAGE}", "1 layout finding(s)."],
            )


if __name__ == "__main__":
    unittest.main()
