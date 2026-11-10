"""Tests of `parity_sample.py` on small repositories in a temporary directory, and on this one."""

import ast
import contextlib
import importlib.util
import io
import re
import tempfile
import unittest
from collections.abc import Mapping
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("parity_sample", HERE / "parity_sample.py")
assert spec and spec.loader
sample = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sample)


def repository(files: Mapping[str, str]) -> tempfile.TemporaryDirectory[str]:
    """A temporary directory that holds `files`, by their paths."""
    directory = tempfile.TemporaryDirectory()
    for path, text in files.items():
        (Path(directory.name) / path).parent.mkdir(parents=True, exist_ok=True)
        (Path(directory.name) / path).write_text(text)
    return directory


LEAN = {
    "EthLib/Execution/Exports.lean": "module\n\npublic import EthLib.Execution.Block\n",
    "EthLib/Execution/Block.lean": (
        "module\n\npublic import Init\n-- import EthLib.Consensus.State\n"
        "public import EthLib.Base.Bytes\n"
    ),
    "EthLib/Base/Bytes.lean": "module\n",
    "EthLib/Consensus/State.lean": "module\n",
    "EthLib/Execution/Proofs/Block.lean": "module\n\npublic import EthLib.Execution.Block\n",
}

PYTHON = {
    "bindings/python/tests/conftest.py": "import archives\n",
    "bindings/python/tests/archives.py": "import json\n",
    "bindings/python/tests/parity/__init__.py": "",
    "bindings/python/tests/parity/test_execution.py": (
        "from . import catalogue\nfrom .runners import run\n"
    ),
    "bindings/python/tests/parity/catalogue.py": "from ..engine.cases import EXCEPTIONS\n",
    "bindings/python/tests/parity/runners.py": (
        "def run():\n    from ethlib.execution import blocks\n"
    ),
    "bindings/python/tests/parity/legacy.py": "",
    "bindings/python/tests/engine/__init__.py": "",
    "bindings/python/tests/engine/cases.py": "import raising\n",
    "bindings/python/tests/raising.py": "",
    "bindings/python/tests/consensus/test_fork.py": "",
    "bindings/python/ethlib/__init__.py": "",
    "bindings/python/ethlib/execution/__init__.py": "",
    "bindings/python/ethlib/execution/blocks/__init__.py": "from ethlib import errors\n",
    "bindings/python/ethlib/errors.py": "",
    "bindings/python/ethlib/consensus/__init__.py": "",
}


class Closure(unittest.TestCase):
    def test_lean_follows_ethlib_imports_and_no_comment(self):
        with repository(LEAN) as root:
            self.assertEqual(
                sample.lean_files(Path(root), ["EthLib.Execution.Exports"]),
                {
                    "EthLib/Execution/Exports.lean",
                    "EthLib/Execution/Block.lean",
                    "EthLib/Base/Bytes.lean",
                },
            )

    def test_python_follows_absolute_relative_and_nested_imports(self):
        with repository(PYTHON) as root:
            self.assertEqual(
                sample.python_files(
                    Path(root), [sample.TEST_MODULE, "bindings/python/tests/conftest.py"]
                ),
                {
                    "bindings/python/tests/conftest.py",
                    "bindings/python/tests/archives.py",
                    "bindings/python/tests/parity/__init__.py",
                    "bindings/python/tests/parity/test_execution.py",
                    "bindings/python/tests/parity/catalogue.py",
                    "bindings/python/tests/parity/runners.py",
                    "bindings/python/tests/engine/__init__.py",
                    "bindings/python/tests/engine/cases.py",
                    "bindings/python/tests/raising.py",
                    "bindings/python/ethlib/__init__.py",
                    "bindings/python/ethlib/execution/__init__.py",
                    "bindings/python/ethlib/execution/blocks/__init__.py",
                    "bindings/python/ethlib/errors.py",
                },
            )

    def test_python_stops_on_an_import_cycle(self):
        cycle = {
            "bindings/python/tests/a.py": "import b\n",
            "bindings/python/tests/b.py": "import a\n",
        }
        with repository(cycle) as root:
            self.assertEqual(
                sample.python_files(Path(root), ["bindings/python/tests/a.py"]),
                {"bindings/python/tests/a.py", "bindings/python/tests/b.py"},
            )


class Reached(unittest.TestCase):
    def reached(self, *changed: str) -> list[str]:
        """The changed paths that the sample reaches, in a repository of LEAN and PYTHON."""
        with repository({**LEAN, **PYTHON}) as root:
            with mock.patch.object(sample, "LEAN_ROOTS", ("EthLib.Execution.Exports",)):
                return sample.reached(Path(root), changed)

    def test_a_reached_path_of_each_kind_runs(self):
        changed = (
            "EthLib/Base/Bytes.lean",
            "bindings/python/ethlib/errors.py",
            "bindings/python/blocks.c",
            "bindings/python/wrappers.h",
            "tests/sources.toml",
            ".github/workflows/ci.yml",
        )
        self.assertEqual(self.reached(*changed), sorted(changed))

    def test_a_new_conftest_on_the_way_to_the_test_runs(self):
        changed = ("bindings/python/tests/parity/conftest.py", "conftest.py")
        self.assertEqual(self.reached(*changed), sorted(changed))

    def test_a_pytest_configuration_runs(self):
        self.assertEqual(self.reached("pytest.ini"), ["pytest.ini"])

    def test_a_conftest_outside_the_import_path_is_read(self):
        with repository({**LEAN, **PYTHON, "conftest.py": "from pathlib import Path\n"}) as root:
            with mock.patch.object(sample, "LEAN_ROOTS", ("EthLib.Execution.Exports",)):
                self.assertEqual(sample.reached(Path(root), ["conftest.py"]), ["conftest.py"])

    def test_an_unreached_path_does_not_run(self):
        self.assertEqual(
            self.reached(
                "EthLib/Consensus/State.lean",
                "EthLib/Execution/Proofs/Block.lean",
                "bindings/python/tests/parity/legacy.py",
                "bindings/python/tests/consensus/test_fork.py",
                "bindings/python/ethlib/consensus/__init__.py",
                "bindings/python/tests/blocks.c",
                "README.md",
            ),
            [],
        )


class Shard(unittest.TestCase):
    def test_the_hash_read_as_a_number_picks_the_shard(self):
        self.assertEqual(sample.shard("00c8", 200), 1)
        self.assertEqual(sample.shard("00c7", 200), 200)
        self.assertEqual(sample.shard("ff", 200), 56)

    def test_every_digit_of_a_full_hash_counts(self):
        # bc gives 0x3d3c42e5aac5ba805825da76410c181273ba90b1 mod 200 = 129.
        self.assertEqual(sample.shard("3d3c42e5aac5ba805825da76410c181273ba90b1", 200), 130)

    def test_every_shard_is_between_one_and_the_count(self):
        shards = {sample.shard(f"{value:04x}", 200) for value in range(1000)}
        self.assertEqual(shards, set(range(1, 201)))

    def test_a_count_below_one_is_refused(self):
        with contextlib.redirect_stderr(io.StringIO()) as errors, self.assertRaises(SystemExit):
            sample.main(["0a", "0"])
        self.assertIn("expected a positive number of shards, got 0", errors.getvalue())


def natives(path: Path) -> set[str]:
    """The native functions that a file of the package imports or calls as `_native.name`."""
    tree = ast.parse(path.read_text(encoding="utf-8"))
    found = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and (node.module or "").endswith("_native"):
            found |= {alias.name for alias in node.names if alias.name.islower()}
        elif (
            isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == "_native"
        ):
            found.add(node.attr)
    return found


def engine_natives(root: Path) -> set[str]:
    """The native functions behind the engine functions that the parity runners call."""
    runners = (root / "bindings/python/tests/parity/runners.py").read_text(encoding="utf-8")
    called = set(re.findall(r"\bengine\.(\w+)\(", runners))
    package = root / "bindings/python/ethlib/engine/__init__.py"
    tree = ast.parse(package.read_text(encoding="utf-8"))
    return {
        node.attr
        for function in tree.body
        if isinstance(function, ast.FunctionDef) and function.name in called
        for node in ast.walk(function)
        if isinstance(node, ast.Attribute)
        and isinstance(node.value, ast.Name)
        and node.value.id == "_native"
    }


# The C symbol that a Lean declaration exports, which a native function of the bindings calls.
EXPORT = re.compile(r"@\[export (\w+)\]")


def exported_in(root: Path) -> dict[str, str]:
    """The Lean file of the library that exports each C symbol."""
    return {
        symbol: path.relative_to(root).as_posix()
        for path in (root / "EthLib").rglob("*.lean")
        for symbol in EXPORT.findall(path.read_text(encoding="utf-8"))
    }


class Repository(unittest.TestCase):
    def test_every_named_path_exists(self):
        modules = [module.replace(".", "/") + ".lean" for module in sample.LEAN_ROOTS]
        for path in [*modules, sample.TEST_MODULE, *sample.FIXED]:
            with self.subTest(path=path):
                self.assertTrue((sample.ROOT / path).is_file())

    def test_each_root_and_a_file_it_imports_run(self):
        roots = [module.replace(".", "/") + ".lean" for module in sample.LEAN_ROOTS]
        imported = [
            "EthLib/Serialization/Rlp.lean",
            "EthLib/Cryptography/Hash/Keccak.lean",
            "EthLib/Engine/NewPayload.lean",
            "bindings/python/tests/parity/runners.py",
        ]
        self.assertEqual(sample.reached(sample.ROOT, roots + imported), sorted(roots + imported))

    def test_the_lean_roots_export_every_native_that_the_runners_reach(self):
        # The engine package holds other functions, whose natives the runners never call.
        # The consensus runners alone call the consensus, networking and KZG packages.
        python = sample.python_files(sample.ROOT, [sample.TEST_MODULE])
        package = [
            sample.ROOT / path
            for path in python
            if path.startswith("bindings/python/ethlib/")
            and not path.startswith(
                (
                    "bindings/python/ethlib/consensus/",
                    "bindings/python/ethlib/engine/",
                    "bindings/python/ethlib/networking/",
                    "bindings/python/ethlib/cryptography/kzg/",
                )
            )
        ]
        called = set().union(*map(natives, package)) | engine_natives(sample.ROOT)
        # The native function `name` calls the C symbol `eth_name`, which one Lean file exports.
        exports = exported_in(sample.ROOT)
        closure = sample.lean_files(sample.ROOT, sample.LEAN_ROOTS)
        self.assertIn("engine_new_payload_on_chain", called)
        for native in sorted(called):
            with self.subTest(native=native):
                self.assertIn(exports[f"eth_{native}"], closure)

    def test_main_prints_the_decision_and_the_shard(self):
        output, errors = io.StringIO(), io.StringIO()
        changed = io.StringIO("README.md\nEthLib/Execution/Exports.lean\n")
        with (
            mock.patch("sys.stdin", changed),
            contextlib.redirect_stdout(output),
            contextlib.redirect_stderr(errors),
        ):
            self.assertEqual(sample.main(["0a", "200"]), 0)
        self.assertEqual(output.getvalue(), "run=true\nshard=11/200\n")
        self.assertEqual(errors.getvalue(), "EthLib/Execution/Exports.lean\n")

    def test_main_without_a_reached_path_does_not_run(self):
        output = io.StringIO()
        with (
            mock.patch("sys.stdin", io.StringIO("README.md\n")),
            contextlib.redirect_stdout(output),
        ):
            self.assertEqual(sample.main(["0a", "200"]), 0)
        self.assertEqual(output.getvalue(), "run=false\nshard=11/200\n")


if __name__ == "__main__":
    unittest.main()
