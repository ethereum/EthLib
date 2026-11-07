"""Check that the Python package converts no value by hand around the native calls."""

import argparse
import ast
import re
import subprocess
import sys
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Final, Literal, TypeGuard

ROOT: Final = Path(__file__).resolve().parent.parent

PACKAGE: Final = Path("bindings/python/ethlib")
ALLOWLIST: Final = Path("scripts/check_python_boundary_allowlist.txt")

# The name of the scope of a statement outside every function.
MODULE: Final = "<module>"

type Rule = Literal[
    "from_bytes", "to_bytes", "fromhex", "hex", "slice", "bytes", "join", "json", "struct"
]

# What each rule finds, as the message of a finding says it.
RULES: Final[dict[Rule, str]] = {
    "from_bytes": "reads an integer from bytes",
    "to_bytes": "writes an integer as bytes",
    "fromhex": "reads bytes from hexadecimal text",
    "hex": "writes bytes as hexadecimal text",
    "slice": "slices a value",
    "bytes": "builds bytes from parts",
    "join": "joins bytes",
    "json": "converts a value to or from JSON text",
    "struct": "imports struct",
}

# The methods whose call converts between bytes and other values by hand, with their rules.
METHODS: Final[dict[str, Rule]] = {
    "from_bytes": "from_bytes",
    "to_bytes": "to_bytes",
    "fromhex": "fromhex",
    "hex": "hex",
}

# The functions of `json` that turn values into text or back.
JSON: Final = frozenset({"loads", "dumps"})

# The built-in functions that build bytes from their parts.
BUILDERS: Final = frozenset({"bytes", "bytearray"})


def is_rule(name: str) -> TypeGuard[Rule]:
    """Whether a name is the name of a rule."""
    return name in RULES


@dataclass(frozen=True, order=True)
class Finding:
    """One hand conversion: its file, line, enclosing function and rule."""

    path: str
    line: int
    function: str
    rule: Rule


def findings(path: str, text: str) -> list[Finding]:
    """Each hand conversion in the text of one Python file."""
    found: list[Finding] = []

    def add(node: ast.expr | ast.stmt, function: str, rule: Rule) -> None:
        found.append(Finding(path, node.lineno, function, rule))

    def visit(node: ast.AST, function: str) -> None:
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef):
            function = node.name if function == MODULE else f"{function}.{node.name}"
        if isinstance(node, ast.Import) and any(n.name == "struct" for n in node.names):
            add(node, function, "struct")
        elif isinstance(node, ast.ImportFrom) and node.module == "struct":
            add(node, function, "struct")
        elif isinstance(node, ast.Subscript) and _has_slice(node.slice):
            add(node, function, "slice")
        elif isinstance(node, ast.Call):
            rule = _call_rule(node)
            if rule is not None:
                add(node, function, rule)
        for child in ast.iter_child_nodes(node):
            visit(child, function)

    visit(ast.parse(text), MODULE)
    return sorted(found)


def _has_slice(index: ast.expr) -> bool:
    if isinstance(index, ast.Tuple):
        return any(isinstance(item, ast.Slice) for item in index.elts)
    return isinstance(index, ast.Slice)


def _call_rule(node: ast.Call) -> Rule | None:
    """The rule that a call breaks, if any."""
    func = node.func
    if isinstance(func, ast.Name):
        # A call with no argument builds empty bytes, which converts nothing.
        return "bytes" if func.id in BUILDERS and (node.args or node.keywords) else None
    if not isinstance(func, ast.Attribute):
        return None
    if func.attr in METHODS:
        return METHODS[func.attr]
    if func.attr in JSON and isinstance(func.value, ast.Name) and func.value.id == "json":
        return "json"
    if func.attr == "join" and isinstance(func.value, ast.Constant):
        return "join" if isinstance(func.value.value, bytes) else None
    return None


def read_allowlist(root: Path) -> tuple[set[tuple[str, str, Rule]], list[str]]:
    """The allowlisted conversions, as file, function and rule, and the malformed lines."""
    path = root / ALLOWLIST
    entries: set[tuple[str, str, Rule]] = set()
    problems: list[str] = []
    if not path.exists():
        return entries, problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        match = re.fullmatch(r"(\S+) (\S+) (\S+)", line)
        if match is not None and is_rule(rule := match.group(3)):
            entries.add((match.group(1), match.group(2), rule))
            continue
        problems.append(
            f"{ALLOWLIST}:{number}: expected `path function rule` with a rule in"
            f" {sorted(RULES)}, got {line!r}"
        )
    return entries, problems


def git(root: Path, *args: str) -> str:
    """The standard output of a git command run at the root."""
    return subprocess.run(
        ["git", *args], check=True, capture_output=True, text=True, cwd=root
    ).stdout


def package_files(root: Path) -> list[str]:
    """The Python files of the package that git tracks or would add, by relative path."""
    listed = git(
        root, "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", str(PACKAGE)
    )
    paths = sorted({name for name in listed.split("\0") if name.endswith(".py")})
    return [path for path in paths if (root / path).is_file()]


def changed_lines(root: Path, base: str) -> dict[str, set[int]]:
    """Map each Python file of the package to the lines that the branch adds to it."""
    merge_base = git(root, "merge-base", base, "HEAD").strip()
    # Fixed prefixes and unquoted paths, whatever the git configuration of the checkout says.
    diff = git(
        root,
        "-c",
        "core.quotePath=false",
        "diff",
        "--unified=0",
        "--no-color",
        "--no-ext-diff",
        "--src-prefix=a/",
        "--dst-prefix=b/",
        merge_base,
        "--",
        str(PACKAGE),
    )
    result: dict[str, set[int]] = {}
    path = None
    for line in diff.splitlines():
        if line.startswith("+++ "):
            target = line[4:]
            path = target[2:] if target.startswith("b/") else None
            continue
        hunk = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", line)
        if hunk and path is not None:
            first = int(hunk.group(1))
            count = int(hunk.group(2)) if hunk.group(2) is not None else 1
            result.setdefault(path, set()).update(range(first, first + count))
    # `git diff` lists no untracked file, so every line of a new file counts.
    untracked = git(root, "ls-files", "-z", "--others", "--exclude-standard", "--", str(PACKAGE))
    for path in filter(None, untracked.split("\0")):
        if not path.endswith(".py"):
            continue
        count = len((root / path).read_text(encoding="utf-8").splitlines())
        result[path] = set(range(1, count + 1))
    return result


def check_all(root: Path) -> list[str]:
    """Each conversion outside the allowlist, and each allowlist entry that matches none."""
    allowed, problems = read_allowlist(root)
    used: set[tuple[str, str, Rule]] = set()
    for path in package_files(root):
        for item in findings(path, (root / path).read_text(encoding="utf-8")):
            key = (item.path, item.function, item.rule)
            if key in allowed:
                used.add(key)
            else:
                problems.append(message(item))
    for path, function, rule in sorted(allowed - used):
        problems.append(f"{ALLOWLIST}: {path} {function} {rule} matches nothing; remove the entry")
    return problems


def check_base(root: Path, base: str) -> list[str]:
    """Each conversion on a line that the branch adds, unless the allowlist names it."""
    allowed, problems = read_allowlist(root)
    for path, lines in sorted(changed_lines(root, base).items()):
        if not path.endswith(".py") or not (root / path).is_file():
            continue
        for item in findings(path, (root / path).read_text(encoding="utf-8")):
            if item.line in lines and (item.path, item.function, item.rule) not in allowed:
                problems.append(message(item))
    return problems


def message(item: Finding) -> str:
    """The report of one conversion."""
    return (
        f"{item.path}:{item.line}: {item.function} {RULES[item.rule]} ({item.rule}); "
        "pass a typed value to the native call instead"
    )


def main(argv: Sequence[str]) -> int:
    """Print each hand conversion that the check finds, and return the exit code."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="check only the lines changed since the merge base")
    args = parser.parse_args(argv[1:])
    problems = check_base(ROOT, args.base) if args.base else check_all(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
