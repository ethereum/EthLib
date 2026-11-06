"""Tests of `check_docstrings.py` on small repositories in a temporary directory."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_docstrings", HERE / "check_docstrings.py")
assert spec and spec.loader
check_docstrings = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_docstrings)

ONE_LINE = '''\
"""The one line of a module."""


def f():
    """
    The summary of a function.

    One sentence on its line.
    Another sentence on its line.

    A list:

    - an item without a full stop
    - another item;
    1. a numbered item

    ```text
    a fenced block, whose lines
    wrap freely
    ```

    An indented block:

        code that wraps
        freely

    >>> f()
    |a table|row|
    https://example.org/a/link
    """


class A:
    """A class on one line."""
'''

MODULE_LINES = '''\
"""
The first line of a module.

A second paragraph.
"""
'''

MODULE_QUOTES_APART = '''\
"""
The one sentence of a module, apart from its quotes.
"""
'''

MODULE_SPLIT = '''"""The first line of a module,
and the rest of its sentence."""
'''

WRAPPED = '''\
def f():
    """
    The summary of a function.

    A sentence that runs past the end of its line and
    wraps onto the next one.
    """
'''

WRAPPED_ITEM = '''\
class A:
    """
    A class.

    - an item that runs past the end of its line and
      wraps onto the next one
    """

    def g(self):
        """A method that wraps its summary
        onto a second line."""
'''


class CheckDocstrings(unittest.TestCase):
    def run_check(self, files: dict[str, str]) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            return check_docstrings.check(root)

    def test_one_line_headers_and_unwrapped_sentences_pass(self) -> None:
        self.assertEqual(self.run_check({"a.py": ONE_LINE}), [])

    def test_a_module_without_a_docstring_passes(self) -> None:
        self.assertEqual(self.run_check({"a.py": "X = 1\n"}), [])

    def test_a_module_docstring_of_several_lines_fails(self) -> None:
        self.assertEqual(
            self.run_check({"a.py": MODULE_LINES}),
            ["a.py:1: the module docstring has more than one line"],
        )

    def test_a_module_docstring_apart_from_its_quotes_fails(self) -> None:
        self.assertEqual(
            self.run_check({"a.py": MODULE_QUOTES_APART}),
            ["a.py:1: the module docstring has more than one line"],
        )

    def test_a_module_docstring_of_one_wrapped_sentence_fails(self) -> None:
        self.assertEqual(
            self.run_check({"a.py": MODULE_SPLIT}),
            ["a.py:1: the module docstring has more than one line"],
        )

    def test_a_wrapped_sentence_fails(self) -> None:
        self.assertEqual(
            self.run_check({"b/c.py": WRAPPED}),
            ["b/c.py:6: a sentence of the docstring of f wraps onto this line"],
        )

    def test_a_wrapped_item_and_a_wrapped_summary_fail(self) -> None:
        self.assertEqual(
            self.run_check({"d.py": WRAPPED_ITEM}),
            [
                "d.py:6: a sentence of the docstring of A wraps onto this line",
                "d.py:11: a sentence of the docstring of g wraps onto this line",
            ],
        )

    def test_hidden_cache_and_excluded_files_are_skipped(self) -> None:
        files = {
            ".venv/lib/e.py": MODULE_LINES,
            "a/__pycache__/f.py": MODULE_LINES,
            "tests/consensus/pq_keys/generate.py": MODULE_LINES,
        }
        self.assertEqual(self.run_check(files), [])

    def test_every_file_is_reported_in_order(self) -> None:
        files = {"b/g.py": MODULE_LINES, "a/h.py": WRAPPED}
        self.assertEqual(
            [problem.split(":")[0] for problem in self.run_check(files)],
            ["a/h.py", "b/g.py"],
        )


if __name__ == "__main__":
    unittest.main()
