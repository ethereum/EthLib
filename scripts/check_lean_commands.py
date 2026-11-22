"""Check that no Lean module of the library runs a command such as `#print` when it is built."""

import importlib.util
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST = Path("scripts/check_lean_commands_allowlist.txt")

# Load the comment stripper of `soundness_facts.py` by path: `scripts` is not a package.
_spec = importlib.util.spec_from_file_location(
    "soundness_facts", Path(__file__).resolve().parent / "soundness_facts.py"
)
assert _spec and _spec.loader
_facts = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_facts)
strip_lean = _facts.strip_lean

# A keyword that starts with `#`, such as `#print`, `#eval` or `#eval!`, read whole.
# A literal such as `#v[1, 2]` or `#[1, 2]` puts `[` right after it, so it is no command.
KEYWORD = r"#[A-Za-z_][A-Za-z0-9_]*!?(?![A-Za-z0-9_!\[])"
# The keyword opens a line, or follows `in`, as in `set_option maxRecDepth 1000 in #eval x`.
COMMAND = re.compile(rf"^[ \t]*{KEYWORD}|\bin[ \t]+{KEYWORD}")


@dataclass(frozen=True, kw_only=True)
class Command:
    """A line of a Lean file that runs a command: its file, its number and its text."""

    path: str
    line: int
    line_text: str


def commands(path: str, text: str) -> list[Command]:
    """The lines of a Lean file that run a `#` command, outside comments and strings."""
    # Blanking comments and strings never makes a keyword, so a file without one needs no blanking.
    if not re.search(KEYWORD, text):
        return []
    # The stripper keeps every newline, so the lines of the code and of the text align.
    lines = text.split("\n")
    return [
        Command(path=path, line=number, line_text=lines[number - 1].strip())
        for number, code in enumerate(strip_lean(text).split("\n"), 1)
        if COMMAND.search(code)
    ]


def read_allowlist(root: Path) -> tuple[dict[tuple[str, str], str], list[str]]:
    """The allowlisted commands under `root`, each with its reason, and the malformed lines."""
    entries: dict[tuple[str, str], str] = {}
    problems: list[str] = []
    path = root / ALLOWLIST
    if not path.exists():
        return entries, problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        # The command comes last, so it may hold the separator itself.
        fields = [field.strip() for field in line.split(" | ", 2)]
        if len(fields) != 3 or not all(fields):
            problems.append(
                f"{ALLOWLIST}:{number}: an entry is `path | reason | command`, on one line"
            )
            continue
        file, reason, command = fields
        if (file, command) in entries:
            problems.append(f"{ALLOWLIST}:{number}: {file} lists `{command}` twice")
            continue
        entries[(file, command)] = reason
    return entries, problems


def check(root: Path) -> list[str]:
    """Every command that a library module runs when it is built, and every stale entry."""
    allowed, problems = read_allowlist(root)
    used = set()
    for file in sorted((root / "EthLib").rglob("*.lean")):
        relative = file.relative_to(root).as_posix()
        for command in commands(relative, file.read_text(encoding="utf-8")):
            key = (command.path, command.line_text)
            if key in allowed:
                used.add(key)
            else:
                problems.append(
                    f"{command.path}:{command.line}: `{command.line_text}` runs at every build; "
                    "check it in CI instead, or list it in the allowlist with a reason"
                )
    for path, command in sorted(set(allowed) - used):
        problems.append(f"{ALLOWLIST}: {path} has no command `{command}`; remove the entry")
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
