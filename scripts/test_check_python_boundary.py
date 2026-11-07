"""Tests of `check_python_boundary.py` on small repositories in a temporary directory."""

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location(
    "check_python_boundary", HERE / "check_python_boundary.py"
)
assert spec and spec.loader
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)

WRAPPER = "bindings/python/ethlib/a/__init__.py"

# Every conversion that the check finds, one per line, each in a function of its own.
CONVERSIONS = """\
import json
import struct
from struct import pack


def read(out):
    return int.from_bytes(out, "little")


def write(n):
    return n.to_bytes(8, "little")


def unhex(text):
    return bytes.fromhex(text)


def tohex(data):
    return data.hex()


def split(out):
    return out[:32]


def pick(out):
    return out[1:, 0]


def build(code):
    return bytes([code])


def build_array(code):
    return bytearray(code)


def concat(items):
    return b"".join(items)


def parse(text):
    return json.loads(text)


def show(value):
    return json.dumps(value)
"""

# Code that converts nothing by hand.
CLEAN = """\
from ethlib.cryptography import _native


def call(data: bytes, read: dict[str, int]) -> list[bytes]:
    empty = bytes()
    words = ", ".join(["a", "b"])
    return [_native.f(data, read["head"], empty, words)]
"""

NESTED = """\
def outer(out):
    def inner(at):
        return out[at:]

    return inner(0)
"""

MODULE_LEVEL = "HEAD = b'abc'[:2]\n"


def problem(line: int, function: str, rule: str, path: str = WRAPPER) -> str:
    what = boundary.RULES[rule]
    return (
        f"{path}:{line}: {function} {what} ({rule}); pass a typed value to the native call instead"
    )


def git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)


def write(root: Path, files: dict[str, str]) -> None:
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


class CheckAll(unittest.TestCase):
    def run_check(self, files: dict[str, str]) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            git(root, "init", "--quiet")
            write(root, files)
            return boundary.check_all(root)

    def test_every_rule_is_found(self) -> None:
        self.assertEqual(
            self.run_check({WRAPPER: CONVERSIONS}),
            [
                problem(2, "<module>", "struct"),
                problem(3, "<module>", "struct"),
                problem(7, "read", "from_bytes"),
                problem(11, "write", "to_bytes"),
                problem(15, "unhex", "fromhex"),
                problem(19, "tohex", "hex"),
                problem(23, "split", "slice"),
                problem(27, "pick", "slice"),
                problem(31, "build", "bytes"),
                problem(35, "build_array", "bytes"),
                problem(39, "concat", "join"),
                problem(43, "parse", "json"),
                problem(47, "show", "json"),
            ],
        )

    def test_clean_code_passes(self) -> None:
        self.assertEqual(self.run_check({WRAPPER: CLEAN}), [])

    def test_a_nested_function_is_named_after_its_outer_function(self) -> None:
        self.assertEqual(self.run_check({WRAPPER: NESTED}), [problem(3, "outer.inner", "slice")])

    def test_code_outside_functions_is_named_module(self) -> None:
        self.assertEqual(self.run_check({WRAPPER: MODULE_LEVEL}), [problem(1, "<module>", "slice")])

    def test_files_outside_the_package_are_skipped(self) -> None:
        files = {"bindings/python/tests/test_a.py": CONVERSIONS, "scripts/a.py": CONVERSIONS}
        self.assertEqual(self.run_check(files), [])

    def test_an_allowlisted_conversion_passes(self) -> None:
        allowed = f"# A comment.\n\n{WRAPPER} outer.inner slice\n"
        files = {WRAPPER: NESTED, str(boundary.ALLOWLIST): allowed}
        self.assertEqual(self.run_check(files), [])

    def test_an_entry_covers_only_its_rule(self) -> None:
        files = {WRAPPER: NESTED, str(boundary.ALLOWLIST): f"{WRAPPER} outer.inner json\n"}
        self.assertEqual(
            self.run_check(files),
            [
                problem(3, "outer.inner", "slice"),
                f"{boundary.ALLOWLIST}: {WRAPPER} outer.inner json matches nothing;"
                " remove the entry",
            ],
        )

    def test_a_stale_entry_fails(self) -> None:
        files = {WRAPPER: CLEAN, str(boundary.ALLOWLIST): f"{WRAPPER} call slice\n"}
        self.assertEqual(
            self.run_check(files),
            [f"{boundary.ALLOWLIST}: {WRAPPER} call slice matches nothing; remove the entry"],
        )

    def test_a_malformed_entry_fails(self) -> None:
        files = {str(boundary.ALLOWLIST): f"{WRAPPER} call\n{WRAPPER} call shift\n"}
        self.assertEqual(
            self.run_check(files),
            [
                f"{boundary.ALLOWLIST}:1: expected `path function rule` with a rule in"
                f" {sorted(boundary.RULES)}, got {WRAPPER + ' call'!r}",
                f"{boundary.ALLOWLIST}:2: expected `path function rule` with a rule in"
                f" {sorted(boundary.RULES)}, got {WRAPPER + ' call shift'!r}",
            ],
        )


class CheckBase(unittest.TestCase):
    def test_only_added_lines_are_reported_even_when_allowlisted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            git(root, "init", "--quiet", "--initial-branch=master")
            git(root, "config", "user.email", "a@example.com")
            git(root, "config", "user.name", "A")
            allowed = f"{WRAPPER} outer.inner slice\n"
            write(root, {WRAPPER: NESTED, str(boundary.ALLOWLIST): allowed})
            git(root, "add", "-A")
            git(root, "commit", "--quiet", "-m", "base")
            git(root, "checkout", "--quiet", "-b", "branch")
            write(root, {WRAPPER: NESTED + "\n\ndef added(out):\n    return out[:4]\n"})
            git(root, "commit", "--quiet", "-am", "change")
            write(root, {"bindings/python/ethlib/b.py": MODULE_LEVEL})
            self.assertEqual(
                boundary.check_base(root, "master"),
                [
                    problem(9, "added", "slice"),
                    problem(1, "<module>", "slice", "bindings/python/ethlib/b.py"),
                ],
            )


if __name__ == "__main__":
    unittest.main()
