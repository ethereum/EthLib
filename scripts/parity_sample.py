"""Say whether a change reaches the execution parity tests, and which shard of them it samples."""

import argparse
import ast
import importlib.util
import sys
from collections.abc import Iterable
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent

# Load the import reader of `check_layers.py` by path: `scripts` is not a package.
_spec = importlib.util.spec_from_file_location("check_layers", ROOT / "scripts" / "check_layers.py")
assert _spec and _spec.loader
_layers = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_layers)

# The modules of the C exports that the runners of the execution parity tests call.
# A test of this script checks that they define every native function that those runners reach.
LEAN_ROOTS = (
    "EthLib.Execution.Exports",
    "EthLib.Engine.Exports.NewPayload",
    "EthLib.Cryptography.Exports.Keccak",
    "EthLib.Serialization.Exports.Rlp",
)
# The test module; pytest also loads each conftest file on the way to it.
TEST_MODULE = "bindings/python/tests/parity/test_execution.py"
# The directories that hold the top-level modules: the pytest pythonpath and the package root.
PYTHON_PATH = ("bindings/python/tests", "bindings/python")
# The files that pin the cases, build the bindings, decide the closures, or define this job.
# The data files that the suite reads at collection are left out: the `suites` job reads them too.
FIXED = frozenset(
    {
        ".github/workflows/ci.yml",
        ".python-version",
        "lake-manifest.json",
        "lakefile.lean",
        "lean-toolchain",
        "pyproject.toml",
        "scripts/check_layers.py",
        "scripts/fetch_archives.py",
        "scripts/parity_sample.py",
        "scripts/soundness_facts.py",
        "setup.py",
        "tests/parity/disagreements.toml",
        "tests/sources.toml",
        "uv.lock",
    }
)
# The files that configure pytest instead of pyproject.toml when one of them exists.
PYTEST_CONFIGS = frozenset({"pytest.ini", "tox.ini", "setup.cfg"})
# The C sources of the extension module, which is built from all of them.
EXTENSION = PurePosixPath("bindings/python")
EXTENSION_SUFFIXES = (".c", ".h")

USAGE = """\
git diff --name-only BASE HEAD | parity_sample.py COMMIT SHARDS

It reads the changed paths on standard input, one per line.
It prints run=true or run=false, then shard=k/n, in the form of GITHUB_OUTPUT.
It prints each changed path that the tests reach on standard error.
"""


def lean_files(root: Path, modules: Iterable[str]) -> set[str]:
    """The files of `modules` and of every EthLib module that they import, directly or not."""
    found: set[str] = set()
    pending = list(modules)
    while pending:
        module = pending.pop()
        path = PurePosixPath(*module.split(".")).with_suffix(".lean").as_posix()
        if module.split(".")[0] != "EthLib" or path in found:
            continue
        found.add(path)
        pending += _layers.imports((root / path).read_text(encoding="utf-8"))
    return found


def _module_files(root: Path, name: str) -> list[str]:
    """The files of the repository that importing the absolute module `name` runs."""
    parts = name.split(".")
    for base in PYTHON_PATH:
        files: list[str] = []
        for depth in range(1, len(parts) + 1):
            stem = PurePosixPath(base, *parts[:depth])
            for candidate in (stem / "__init__.py", stem.with_suffix(".py")):
                if (root / candidate).is_file():
                    files.append(candidate.as_posix())
        if files:
            return files
    return []


def _package(path: str) -> list[str]:
    """The package parts of a file under the import path, or none for a file outside it."""
    for base in PYTHON_PATH:
        if PurePosixPath(path).is_relative_to(base):
            return list(PurePosixPath(path).relative_to(base).parent.parts)
    return []


def _imported(root: Path, path: str) -> list[str]:
    """The files of the repository that the imports of one Python file run."""
    names: list[str] = []
    for node in ast.walk(ast.parse((root / path).read_text(encoding="utf-8"), path)):
        if isinstance(node, ast.Import):
            names += [alias.name for alias in node.names]
        elif isinstance(node, ast.ImportFrom):
            # A relative import starts from the file's package, one level up per extra dot.
            parts = _package(path) if node.level else []
            package = parts[: len(parts) - node.level + 1] if node.level else []
            module = ".".join([*package, *([node.module] if node.module else [])])
            names += [module, *(f"{module}.{alias.name}" for alias in node.names)]
    return [file for name in names if name for file in _module_files(root, name)]


def python_files(root: Path, paths: Iterable[str]) -> set[str]:
    """The files of `paths` and of every repository module that they import, directly or not."""
    found: set[str] = set()
    pending = list(paths)
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        pending += _imported(root, path)
    return found


def conftests(path: str) -> list[str]:
    """The conftest file of each directory above a test file, which pytest loads if it exists."""
    return [(parent / "conftest.py").as_posix() for parent in PurePosixPath(path).parents]


def reached(root: Path, changed: Iterable[str]) -> list[str]:
    """The changed paths that the execution parity tests read, build from or run."""
    loaded = conftests(TEST_MODULE)
    present = [path for path in loaded if (root / path).is_file()]
    files = FIXED | lean_files(root, LEAN_ROOTS) | python_files(root, [TEST_MODULE, *present])
    return sorted(
        path
        for path in changed
        if path in files
        or path in loaded
        or path in PYTEST_CONFIGS
        or (PurePosixPath(path).parent == EXTENSION and path.endswith(EXTENSION_SUFFIXES))
    )


def shard(commit: str, count: int) -> int:
    """The shard that a commit samples: its hash as a number, modulo `count`, plus one."""
    return int(commit, 16) % count + 1


def _positive(text: str) -> int:
    """A positive number of shards, read from the command line."""
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError(f"expected a positive number of shards, got {value}")
    return value


def main(arguments: list[str]) -> int:
    """Print whether the changed paths on standard input reach the tests, and the shard."""
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=USAGE,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("commit", help="the hexadecimal hash of the commit that picks the shard")
    parser.add_argument("shards", type=_positive, help="the number of shards")
    options = parser.parse_args(arguments)
    changed = [line.strip() for line in sys.stdin if line.strip()]
    hits = reached(ROOT, changed)
    for path in hits:
        print(path, file=sys.stderr)
    print(f"run={'true' if hits else 'false'}")
    print(f"shard={shard(options.commit, options.shards)}/{options.shards}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
