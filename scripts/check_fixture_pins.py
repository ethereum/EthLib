"""Check that the test vectors and fixtures cite only the pins of `tests/sources.toml`."""

import ast
import json
import os
import re
import sys
import tomllib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent

SOURCES = "tests/sources.toml"
TREES = ("tests", "bindings/python/tests")
# A commit cited as "commit <sha>", as a "Commit: <sha>" line, or in a `/blob/` or `/tree/` link.
COMMIT = re.compile(r"(?:\b[Cc]ommit:?[\s#`]*|/(?:blob|tree)/)(?=[0-9a-f]*[0-9])([0-9a-f]{7,40})\b")
# A hexadecimal word of 7 to 40 digits, with a letter and a digit, that reads as a commit.
# It is one in backticks, or after "at", as in "execution-specs at `2c0c8e7`".
_HEX = r"(?=[0-9a-f]*[0-9])(?=[0-9a-f]*[a-f])([0-9a-f]{7,40})"
HEX_QUOTED = re.compile(rf"`{_HEX}`")
HEX_AT = re.compile(rf"\bat\s+{_HEX}\b")
FULL_COMMIT = re.compile(r"[0-9a-f]{40}")
SHA256 = re.compile(r"[0-9a-f]{64}")
SOURCE_LINE = "# Source: "

GENERATORS = "tests/generators.toml"
# EthLib itself, and a generator that no record names, need no definition.
RESERVED = ("ethlib", "not established")
GROUP_FIELDS = {"cases", "subset", "generator", "checked"}
# A licence or a Python file pins no case.
NOT_A_CASE = re.compile(r"(?:^|/)LICENSE$|\.py$")
# The tests that import the runtime oracles, and the lock file that pins their versions.
TESTS = "bindings/python/tests"
LOCK = "uv.lock"
# The cache of the release archives, where `fetch_archives.members` lists the files of each one.
ARCHIVES = "ETHLIB_ARCHIVES"


def scanned_files(root: Path) -> list[Path]:
    """The files under the test trees that can cite a commit."""
    files = []
    for tree in TREES:
        for path in sorted((root / tree).rglob("*")):
            if path.is_file() and (path.suffix in (".py", ".md") or path.name == "SHA256SUMS"):
                files.append(path)
    return files


def readme(directory: Path, root: Path) -> Path | None:
    """The README of a directory: its own, or else the nearest one above it inside `root`."""
    for candidate in (directory, *directory.parents):
        if candidate == root or root not in candidate.parents:
            return None
        if (candidate / "README.md").is_file():
            return candidate / "README.md"
    return None


def pinned_files(directory: Path) -> list[str]:
    """The files that the SHA256SUMS of a directory pins, relative to the directory."""
    lines = (directory / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    return [
        line.split(maxsplit=1)[1] for line in lines if line.strip() and not line.startswith("#")
    ]


def glob_pattern(glob: str) -> re.Pattern[str]:
    """A glob as a pattern: `**` matches across directories, `*` and `?` within one name."""
    parts = re.split(r"(\*\*|\*|\?)", glob)
    wildcards = {"**": ".*", "*": "[^/]*", "?": "[^/]"}
    return re.compile("".join(wildcards.get(part, re.escape(part)) for part in parts))


def check_groups(
    where: str, groups: Any, defined: dict[str, Any], files: list[str] | None, complete: bool
) -> tuple[list[str], set[str]]:
    """The problems of the groups of one directory or archive, and the generators they name."""
    # `files` lists the pinned files of a directory, or the members of an archive.
    # It is None for an archive whose member list is not in the cache.
    # A directory is `complete`: each of its pinned files belongs to a group.
    # An archive is not, since a source archive also holds a README, a Makefile and the like.
    problems: list[str] = []
    named: set[str] = set()
    if not isinstance(groups, list) or not groups:
        return [f"{GENERATORS}: {where} needs at least one group"], named
    patterns: list[tuple[list[re.Pattern[str]], bool]] = []
    for index, group in enumerate(groups, 1):
        label = f"{GENERATORS}: {where}, group {index}"
        for field in sorted(set(group) - GROUP_FIELDS):
            problems.append(f"{label}: unknown field {field}")
        cases = group.get("cases")
        if not isinstance(cases, list) or not cases or not all(isinstance(c, str) for c in cases):
            problems.append(f"{label}: needs a list of globs in cases")
            cases = []
        generator = group.get("generator", "")
        named.add(generator)
        if generator not in defined and generator not in RESERVED:
            problems.append(f"{label}: the generator '{generator}' is not defined")
        if (generator == "not established") != bool(group.get("checked")):
            problems.append(
                f"{label}: needs checked when, and only when, the generator is not established"
            )
        globs = [glob_pattern(case) for case in cases]
        patterns.append((globs, bool(group.get("subset"))))
        if files is not None:
            kind = "pinned file" if complete else "member of the archive"
            for case, pattern in zip(cases, globs, strict=True):
                if not any(pattern.fullmatch(f) for f in files):
                    problems.append(f"{label}: {case} matches no {kind}")
    for name in files or []:
        if NOT_A_CASE.search(name):
            continue
        owners = [subset for globs, subset in patterns if any(g.fullmatch(name) for g in globs)]
        if not owners:
            if complete:
                problems.append(f"{GENERATORS}: {where}/{name} belongs to no group")
        elif len(owners) > 1 and not all(owners):
            problems.append(
                f"{GENERATORS}: {where}/{name} is in several groups, so each needs a subset"
            )
    return problems, named


def check_generators(
    root: Path, directories: set[str], archives: set[str], members: dict[str, list[str]]
) -> list[str]:
    """Every problem of the generator records, against the directories and archives of the pins."""
    path = root / GENERATORS
    if not path.is_file():
        return [f"{GENERATORS} is missing"]
    config = tomllib.loads(path.read_text(encoding="utf-8"))
    defined: dict[str, Any] = config.get("generators", {})
    problems = []
    for name, entry in defined.items():
        if name in RESERVED:
            problems.append(f"{GENERATORS}: the generator '{name}' is reserved")
        for field in ("computes", "version", "source"):
            if not entry.get(field):
                problems.append(f"{GENERATORS}: the generator '{name}' needs {field}")
        modules = entry.get("imports", [])
        if not isinstance(modules, list) or not all(isinstance(m, str) for m in modules):
            problems.append(
                f"{GENERATORS}: the generator '{name}' needs a list of names in imports"
            )
            entry["imports"] = []
    named: set[str] = set()
    # The modules that the scripts of a directory import, under each generator of the directory.
    imported: dict[str, set[str]] = {}
    for table, keys in (("directories", directories), ("archives", archives)):
        recorded = config.get(table, {})
        for key in sorted(keys - set(recorded)):
            problems.append(f"{GENERATORS}: {key} has no entry in the table {table}")
        for key in sorted(set(recorded) - keys):
            problems.append(f"{GENERATORS}: {key} is in the table {table}, but not in {SOURCES}")
        for key in sorted(keys & set(recorded)):
            directory = root / key
            if table == "archives":
                files, complete = members.get(key), False
            elif (directory / "SHA256SUMS").is_file():
                files, complete = pinned_files(directory), True
            else:
                files, complete = None, True
            found, used = check_groups(key, recorded[key], defined, files, complete)
            problems += found
            named |= used
            if table == "directories":
                scripts = script_imports(directory)
                allowed = {m for g in used for m in defined.get(g, {}).get("imports", [])}
                for module in sorted(scripts - allowed):
                    problems.append(
                        f"{GENERATORS}: a script in {key} imports {module}, "
                        "which no generator of the directory names in imports"
                    )
                for generator in used:
                    imported.setdefault(generator, set()).update(scripts)
    for name in sorted(set(defined) - named):
        problems.append(f"{GENERATORS}: the generator '{name}' is defined but no group names it")
    for name, entry in sorted(defined.items()):
        for module in sorted(set(entry.get("imports", [])) - imported.get(name, set())):
            problems.append(
                f"{GENERATORS}: the generator '{name}' names {module} in imports, "
                "which no script of its directories imports"
            )
    return problems + check_runtime(root, config.get("runtime", {}))


def imports_of(path: Path) -> set[str]:
    """The top-level names of the absolute imports of one Python file."""
    names = set()
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.Import):
            names.update(alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            names.add(node.module.split(".")[0])
    return names


def imported_modules(root: Path) -> set[str]:
    """The top-level names of the absolute imports of the Python tests."""
    names = set()
    for path in sorted((root / TESTS).rglob("*.py")):
        names |= imports_of(path)
    return names


def script_imports(directory: Path) -> set[str]:
    """The modules from outside the repository that the Python scripts of a directory import."""
    # Python runs a script with the script's own directory first on the import path.
    # So a module or a package next to the script is local, and needs no record.
    names = set()
    for path in sorted(directory.rglob("*.py")):
        siblings = {p.stem if p.suffix == ".py" else p.name for p in path.parent.iterdir()}
        names |= imports_of(path) - siblings
    return names - set(sys.stdlib_module_names) - {"ethlib"}


def locked_versions(root: Path) -> dict[str, str]:
    """The version of each package in the lock file, by its normalized name."""
    path = root / LOCK
    if not path.is_file():
        return {}
    lock = tomllib.loads(path.read_text(encoding="utf-8"))
    return {normalized(p["name"]): p.get("version", "") for p in lock.get("package", [])}


def normalized(package: str) -> str:
    """A package name in the normal form of PEP 503."""
    return re.sub(r"[-_.]+", "-", package).lower()


def check_runtime(root: Path, runtime: dict[str, Any]) -> list[str]:
    """Every problem of the table `runtime` against the imports of the tests and the lock file."""
    problems = []
    # Each tool gives the reason it computes no expected value.
    # So an oracle that moves to the tools fails until someone writes down why.
    reasons = runtime.get("tools", {})
    if not isinstance(reasons, dict):
        problems.append(f"{GENERATORS}: runtime.tools needs a table of modules and reasons")
        reasons = {}
    for module, reason in sorted(reasons.items()):
        if not isinstance(reason, str) or not reason.strip():
            problems.append(f"{GENERATORS}: the tool {module} needs a reason")
    tools = set(reasons)
    oracles: dict[str, Any] = runtime.get("oracles", {})
    for module in sorted(tools & set(oracles)):
        problems.append(f"{GENERATORS}: {module} is both a tool and an oracle")
    imported = imported_modules(root)
    tests = root / TESTS
    # `pythonpath` puts the top of the tests on the import path, and no directory below it.
    # So only a module or a package at the top imports by its bare name.
    local = {p.stem if p.suffix == ".py" else p.name for p in tests.iterdir()}
    external = imported - set(sys.stdlib_module_names) - local - {"ethlib"}
    for module in sorted(external - tools - set(oracles)):
        problems.append(
            f"{GENERATORS}: the tests import {module}, which the table runtime does not list"
        )
    for module in sorted((tools | set(oracles)) - imported):
        problems.append(f"{GENERATORS}: the table runtime lists {module}, which no test imports")
    versions = locked_versions(root)
    for module, entry in sorted(oracles.items()):
        if not entry.get("computes"):
            problems.append(f"{GENERATORS}: the oracle {module} needs computes")
        if "path" in entry:
            if not (root / entry["path"]).is_file():
                problems.append(
                    f"{GENERATORS}: the oracle {module} names a missing file {entry['path']}"
                )
        elif entry.get("package") == "python":
            if module not in sys.stdlib_module_names:
                problems.append(f"{GENERATORS}: the oracle {module} is not in the standard library")
        else:
            locked = versions.get(normalized(entry.get("package", "")))
            if locked is None or locked != entry.get("version"):
                problems.append(
                    f"{GENERATORS}: the oracle {module} has version {entry.get('version')}, "
                    f"but {LOCK} has {locked}"
                )
    return problems


def archive_members(root: Path, cache: Path | None) -> dict[str, list[str]]:
    """The files of each archive whose member list is already in the cache, by archive name."""
    # The check downloads nothing, so an archive that was never listed stays unchecked.
    if cache is None:
        return {}
    config = tomllib.loads((root / SOURCES).read_text(encoding="utf-8"))
    members = {}
    for name, entry in config.get("archives", {}).items():
        listing = cache / f"{entry.get('sha256', '')}.members.json"
        if listing.is_file():
            members[name] = json.loads(listing.read_text(encoding="utf-8"))
    return members


def check(root: Path, members: dict[str, list[str]] | None = None) -> list[str]:
    """Every problem in the repository at `root`, one line each."""
    # `members` gives the files of the archives whose groups are checked against them.
    problems = []
    config = tomllib.loads((root / SOURCES).read_text(encoding="utf-8"))
    repositories = config.get("repositories", {})
    others = config.get("other", {})

    pins = {}
    expected: dict[str, set[str]] = {}
    for name, entry in repositories.items():
        commit = entry.get("commit", "")
        if not FULL_COMMIT.fullmatch(commit):
            problems.append(f"{SOURCES}: {name} needs a full 40-digit commit")
            continue
        pins[name] = commit
        for directory in entry.get("directories", []):
            expected.setdefault(directory, set()).add(f"{name} at {commit}")
    for directory, description in others.items():
        expected.setdefault(directory, set()).add(description)

    pinned = sorted(
        {
            p.parent.relative_to(root).as_posix()
            for tree in TREES
            for p in (root / tree).rglob("SHA256SUMS")
        }
    )
    for directory in sorted(set(pinned) - set(expected)):
        problems.append(f"{directory}: a pinned vector directory that {SOURCES} does not list")
    for directory in sorted(set(expected) - set(pinned)):
        problems.append(f"{SOURCES}: {directory} holds no SHA256SUMS")

    for directory in sorted(set(pinned) & set(expected)):
        sums = root / directory / "SHA256SUMS"
        named = {
            line[len(SOURCE_LINE) :].strip()
            for line in sums.read_text(encoding="utf-8").splitlines()
            if line.startswith(SOURCE_LINE)
        }
        for source in sorted(expected[directory] - named):
            problems.append(f"{directory}/SHA256SUMS: missing the line '{SOURCE_LINE}{source}'")
        for source in sorted(named - expected[directory]):
            problems.append(
                f"{directory}/SHA256SUMS: '{SOURCE_LINE}{source}' is not a source "
                f"that {SOURCES} lists for this directory"
            )
        commits = {
            name: pins[name]
            for name, entry in repositories.items()
            if name in pins and directory in entry.get("directories", [])
        }
        if commits:
            document = readme(root / directory, root)
            text = document.read_text(encoding="utf-8") if document else ""
            for name, commit in sorted(commits.items()):
                where = document.relative_to(root) if document else f"{directory}: no README"
                problem = f"{where}: does not name {name} at {commit}"
                if commit not in text and problem not in problems:
                    problems.append(problem)

    archives = config.get("archives", {})
    for name, entry in archives.items():
        # An archive from no repository, such as a NIST zip file, gives a `source` instead.
        if "repository" in entry or not entry.get("source"):
            if entry.get("repository") not in repositories:
                problems.append(
                    f"{SOURCES}: the archive {name} needs a recorded repository, "
                    "or a source that is no repository"
                )
        if not str(entry.get("url", "")).startswith("https://"):
            problems.append(f"{SOURCES}: the archive {name} needs an https URL")
        size = entry.get("size")
        if type(size) is not int or size <= 0:
            problems.append(f"{SOURCES}: the archive {name} needs a positive size in bytes")
        if not SHA256.fullmatch(str(entry.get("sha256", ""))):
            problems.append(f"{SOURCES}: the archive {name} needs a 64-digit sha256")

    problems += check_generators(root, set(expected), set(archives), members or {})

    cited, named = set(), set()
    for path in scanned_files(root):
        text = path.read_text(encoding="utf-8")
        # A test names a release archive by its key in the table `archives`, in double quotes.
        named.update(name for name in archives if f'"{name}"' in text)
        starts = {}
        for pattern in (COMMIT, HEX_QUOTED, HEX_AT):
            for match in pattern.finditer(text):
                starts.setdefault(match.start(1), match.group(1))
        for start, short in sorted(starts.items()):
            line = text.count("\n", 0, start) + 1
            # A short commit must be a prefix of a pin.
            owners = [name for name, commit in pins.items() if commit.startswith(short)]
            if owners:
                cited.add(owners[0])
            else:
                problems.append(
                    f"{path.relative_to(root)}:{line}: cites commit {short}, "
                    f"which is not a pin of {SOURCES}"
                )
        for name, commit in pins.items():
            if commit in text:
                cited.add(name)
    for name in sorted(set(pins) - cited):
        problems.append(f"{SOURCES}: no test cites the pin of {name}")
    for name in sorted(set(archives) - named):
        problems.append(f"{SOURCES}: no test names the archive {name}")
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    cache = os.environ.get(ARCHIVES, "")
    members = archive_members(ROOT, Path(cache) if cache else None)
    problems = check(ROOT, members)
    for problem in problems:
        print(problem, file=sys.stderr)
    if not problems:
        print(f"Every test cites the pins of {SOURCES}.")
        if members:
            print(f"The groups of {len(members)} archives match their member lists in {cache}.")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
