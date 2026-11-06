"""Check that the test vectors and fixtures cite only the pins of `tests/sources.toml`."""

import re
import sys
import tomllib
from pathlib import Path

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


def check(root: Path) -> list[str]:
    """Every problem in the repository at `root`, one line each."""
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
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    if not problems:
        print(f"Every test cites the pins of {SOURCES}.")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
