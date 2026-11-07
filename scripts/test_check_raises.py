"""Tests of `check_raises.py` on small repositories in a temporary directory."""

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_raises", HERE / "check_raises.py")
assert spec and spec.loader
check_raises = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_raises)

HELPER = """\
import re

import pytest


def raises(exception, message):
    return pytest.raises(exception, match=rf"\\A{re.escape(message)}\\Z")
"""

THROUGH_HELPER = """\
from raising import raises


def test_a():
    with raises(ValueError, "bad length: 3"):
        int("x")
"""

FRAGMENT = """\
import pytest


def test_a():
    with pytest.raises(ValueError, match=r"length"):
        int("x")
"""

NO_MATCH = """\
import pytest


def test_a():
    with pytest.raises(ValueError):
        int("x")
"""

ALIASED = """\
import pytest as pt


def test_a():
    with pt.raises(ValueError, match=r"\\Abad\\Z"):
        int("x")
"""

FROM_IMPORT = """\
from pytest import RaisesExc, raises


def test_a():
    with raises(ValueError):
        int("x")
"""

UNCALLED = """\
import pytest

expect = pytest.raises
"""

NOT_A_CALL = """\
# pytest.raises(ValueError) in a comment is not a use.
TEXT = "pytest.raises(ValueError, match='x')"


def test_a(excinfo):
    excinfo.raises(ValueError)
"""

RUNNER = """\
import pytest


def run_case(case):
    with pytest.raises(ValueError) as error:
        int(case)
    assert case.names(str(error.value))


def other(case):
    with pytest.raises(ValueError):
        int(case)
"""

RUNNER_FRAGMENT = """\
import pytest


def run_case(case):
    with pytest.raises(ValueError, match="length"):
        int(case)
"""

SHAPED = """\
from raising import raises_shape


def test_a(n):
    with raises_shape(ValueError, "decoding: inputTooShort {n} {n}"):
        int("x")
    with raises_shape(ValueError, f"decoding: field {n}: wrongLength 20 {{n}}"):
        int("x")
"""


def shape_case(template: str) -> str:
    call = f"with raises_shape(ValueError, {template!r}):\n    pass\n"
    return "from raising import raises_shape\n\n" + call


SHAPE_ELSEWHERE = """\
from helpers import raises_shape
"""

SHAPE_DEFINED = """\
def raises_shape(exception, template):
    return exception
"""

ALLOWED = "runner.py run_case: the vectors name no message\n"


def problem(path: str, line: int, what: str) -> str:
    return f"{path}:{line}: {what}; expect an exception with raises() of raising.py"


class CheckRaises(unittest.TestCase):
    def run_check(self, files: dict[str, str]) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "--quiet"], cwd=root, check=True)
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            return check_raises.check(root)

    def test_the_helper_and_its_callers_pass(self) -> None:
        files = {
            str(check_raises.HELPER): HELPER,
            "bindings/python/tests/a/test_a.py": THROUGH_HELPER,
        }
        self.assertEqual(self.run_check(files), [])

    def test_a_fragment_fails(self) -> None:
        self.assertEqual(
            self.run_check({"bindings/python/tests/a/test_a.py": FRAGMENT}),
            [problem("bindings/python/tests/a/test_a.py", 5, "calls pytest.raises")],
        )

    def test_a_call_without_match_fails(self) -> None:
        self.assertEqual(
            self.run_check({"scripts/test_b.py": NO_MATCH}),
            [problem("scripts/test_b.py", 5, "calls pytest.raises")],
        )

    def test_an_alias_of_pytest_fails(self) -> None:
        self.assertEqual(
            self.run_check({"test_c.py": ALIASED}), [problem("test_c.py", 5, "calls pt.raises")]
        )

    def test_an_import_from_pytest_fails(self) -> None:
        self.assertEqual(
            self.run_check({"test_d.py": FROM_IMPORT}),
            [
                problem("test_d.py", 1, "imports RaisesExc from pytest"),
                problem("test_d.py", 1, "imports raises from pytest"),
            ],
        )

    def test_a_reference_without_a_call_fails(self) -> None:
        self.assertEqual(
            self.run_check({"conftest.py": UNCALLED}),
            [problem("conftest.py", 3, "uses pytest.raises")],
        )

    def test_text_and_other_objects_pass(self) -> None:
        self.assertEqual(self.run_check({"test_e.py": NOT_A_CALL}), [])

    def test_the_helper_elsewhere_fails(self) -> None:
        self.assertEqual(
            self.run_check({"bindings/python/raising.py": HELPER}),
            [
                problem("bindings/python/raising.py", 7, "calls pytest.raises"),
                "bindings/python/raising.py:6: defines raises; import it from raising",
            ],
        )

    def test_ignored_files_are_skipped(self) -> None:
        files = {
            ".gitignore": "build/\nvenv/\n",
            "build/lib/test_f.py": NO_MATCH,
            "venv/lib/test_g.py": NO_MATCH,
        }
        self.assertEqual(self.run_check(files), [])

    def test_every_file_is_reported_in_order(self) -> None:
        files = {"b/test_h.py": NO_MATCH, "a/test_i.py": FRAGMENT}
        self.assertEqual(
            [problem.split(":")[0] for problem in self.run_check(files)],
            ["a/test_i.py", "b/test_h.py"],
        )

    def test_an_allowlisted_function_passes_only_with_a_bare_call(self) -> None:
        files = {str(check_raises.ALLOWLIST): ALLOWED, "runner.py": RUNNER}
        self.assertEqual(self.run_check(files), [problem("runner.py", 11, "calls pytest.raises")])

    def test_an_allowlisted_function_with_a_pattern_fails(self) -> None:
        files = {str(check_raises.ALLOWLIST): ALLOWED, "runner.py": RUNNER_FRAGMENT}
        self.assertEqual(
            self.run_check(files),
            [
                problem("runner.py", 5, "calls pytest.raises"),
                "scripts/check_raises_allowlist.txt: runner.py run_case has no bare pytest.raises"
                " call; remove the entry",
            ],
        )

    def test_a_stale_entry_fails(self) -> None:
        files = {str(check_raises.ALLOWLIST): ALLOWED, "runner.py": THROUGH_HELPER}
        self.assertEqual(
            self.run_check(files),
            [
                "scripts/check_raises_allowlist.txt: runner.py run_case has no bare pytest.raises"
                " call; remove the entry"
            ],
        )

    def test_an_entry_without_a_reason_fails(self) -> None:
        files = {str(check_raises.ALLOWLIST): "# A comment.\n\nrunner.py run_case:\n"}
        self.assertEqual(
            self.run_check(files),
            [
                "scripts/check_raises_allowlist.txt:3: an entry is `path function: reason`,"
                " on one line"
            ],
        )

    def test_a_template_of_text_and_numbers_passes(self) -> None:
        self.assertEqual(self.run_check({"test_j.py": SHAPED}), [])

    def test_a_template_with_an_alternation_fails(self) -> None:
        self.assertEqual(
            self.run_check({"test_k.py": shape_case("inputTooShort|trailingBytes {n}")}),
            ["test_k.py:3: gives raises_shape a template beyond text and {n}"],
        )

    def test_a_template_with_a_wildcard_fails(self) -> None:
        self.assertEqual(
            self.run_check({"test_l.py": shape_case("decoding: .*")}),
            ["test_l.py:3: gives raises_shape a template beyond text and {n}"],
        )

    def test_a_template_with_a_regex_fails(self) -> None:
        for template in ("field \\d+: listAsBytes", "wrongLength {m}", "a{2}"):
            with self.subTest(template=template):
                self.assertEqual(
                    self.run_check({"test_m.py": shape_case(template)}),
                    ["test_m.py:3: gives raises_shape a template beyond text and {n}"],
                )

    def test_raises_shape_from_another_module_fails(self) -> None:
        self.assertEqual(
            self.run_check({"test_n.py": SHAPE_ELSEWHERE}),
            ["test_n.py:1: imports raises_shape from helpers"],
        )

    def test_raises_shape_defined_outside_the_helper_fails(self) -> None:
        self.assertEqual(
            self.run_check({"test_o.py": SHAPE_DEFINED}),
            ["test_o.py:1: defines raises_shape; import it from raising"],
        )


if __name__ == "__main__":
    unittest.main()
