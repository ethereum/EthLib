"""Reject additions to a theorem baseline already present at the base revision."""

import argparse
import stat
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = Path("scripts/check_theorems_baseline.txt")


class BaselineError(ValueError):
    """An invalid baseline or an unavailable Git revision."""


def git(root: Path, *args: str) -> str:
    """Read the output of Git without invoking a shell."""
    try:
        result = subprocess.run(
            ["git", *args], cwd=root, capture_output=True, text=True, encoding="utf-8", check=False
        )
    except (OSError, UnicodeError) as error:
        raise BaselineError(str(error)) from error
    if result.returncode:
        raise BaselineError(result.stderr.strip() or "Git command failed")
    return result.stdout


def entries(text: str, source: str) -> set[tuple[str, str]]:
    """Parse module and declaration pairs, rejecting malformed and duplicate entries."""
    found: set[tuple[str, str]] = set()
    for number, line in enumerate(text.splitlines(), 1):
        words = line.partition("#")[0].split()
        if not words:
            continue
        if len(words) != 2:
            raise BaselineError(f"{source}:{number}: expected a module and a declaration name")
        entry = (words[0], words[1])
        if entry in found:
            raise BaselineError(f"{source}:{number}: duplicate baseline entry")
        found.add(entry)
    return found


def baseline_at(root: Path, commit: str) -> str | None:
    """Read the baseline blob, or return nothing when the commit has no baseline."""
    record = git(root, "ls-tree", "-z", commit, "--", BASELINE.as_posix())
    if not record:
        return None
    # The exact pathspec yields one record, `<mode> <type> <object>\t<path>`.
    mode, _, blob = record.partition("\t")[0].split()
    # Only these two modes name a regular file; each implies the blob type.
    if mode not in {"100644", "100755"}:
        raise BaselineError(f"{BASELINE} at {commit}: expected a regular file")
    return git(root, "cat-file", "blob", blob)


def comparison(root: Path, base: str) -> tuple[list[str], bool]:
    """Return added entries and whether this change creates the baseline."""
    if not base:
        raise BaselineError("the base revision must name a commit")
    try:
        commit = git(
            root, "rev-parse", "--verify", "--end-of-options", f"{base}^{{commit}}"
        ).strip()
    except BaselineError as error:
        raise BaselineError(f"invalid base revision {base!r}: {error}") from error
    path = root / BASELINE
    try:
        mode = path.lstat().st_mode
        if not stat.S_ISREG(mode):
            raise BaselineError(f"{path}: expected a regular file")
        current = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        current = None
    except (OSError, UnicodeError) as error:
        raise BaselineError(f"{path}: {error}") from error
    current_entries = entries(current or "", str(BASELINE))
    previous = baseline_at(root, commit)
    if previous is None:
        return [], current is not None
    if current is None:
        raise BaselineError(f"{BASELINE}: missing from the working tree but present at {base}")
    previous_entries = entries(previous, f"{BASELINE} at {base}")
    added = sorted(current_entries - previous_entries)
    problems = [f"{BASELINE}: entry added since {base}: {module} {decl}" for module, decl in added]
    return problems, False


def check(root: Path, base: str) -> list[str]:
    """Find every entry added to an existing baseline since the base commit."""
    return comparison(root, base)[0]


def main(argv: list[str] | None = None) -> int:
    """Check the baseline against the required base revision."""
    parser = argparse.ArgumentParser(description=__doc__, prog="check-theorems-baseline")
    parser.add_argument("--base", required=True, help="Compare with this Git commit or reference.")
    args = parser.parse_args(argv)
    try:
        problems, initial = comparison(ROOT, args.base)
    except BaselineError as error:
        print(f"check-theorems-baseline: {error}", file=sys.stderr)
        return 2
    for problem in problems:
        print(problem)
    if problems:
        print(f"check-theorems-baseline: added entries: {len(problems)}")
        return 1
    if initial:
        print(
            "check-theorems-baseline: initial baseline creation allowed "
            f"(no baseline at {args.base})"
        )
    else:
        print(f"check-theorems-baseline: no entries added since {args.base}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
