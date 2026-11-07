"""Check that every Python test expects an exception by its whole message, through one helper."""

import ast
import re
import subprocess
import sys
from pathlib import Path
from typing import TypeGuard

ROOT = Path(__file__).resolve().parent.parent

# The one module that may call pytest's exception matchers.
HELPER = Path("bindings/python/tests/raising.py")
ALLOWLIST = Path("scripts/check_raises_allowlist.txt")

# The names of pytest that expect an exception and take a pattern for its message.
MATCHERS = {"raises", "RaisesExc", "RaisesGroup"}

# The names that the helper module defines, which every other module imports from it.
HELPERS = {"raises", "raises_shape", "shape_pattern"}

# The mark of a number in a template of raises_shape, and what a template may not hold besides.
NUMBER = "{n}"
NOT_IN_TEMPLATE = ("|", ".*", "{", "}", "\\")


def read_allowlist(root: Path) -> tuple[dict[tuple[str, str], str], list[str]]:
    """The allowlisted functions, each with its reason, and the malformed lines."""
    path = root / ALLOWLIST
    entries, problems = {}, []
    if not path.exists():
        return entries, problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        match = re.fullmatch(r"(\S+)\s+(\S+):\s*(.*\S)?\s*", line)
        if not match or not match.group(3):
            problems.append(
                f"{ALLOWLIST}:{number}: an entry is `path function: reason`, on one line"
            )
            continue
        entries[(match.group(1), match.group(2))] = match.group(3)
    return entries, problems


def python_files(root: Path) -> list[Path]:
    """The Python files that git tracks or would add under the root, by relative path."""
    # Ignored files, such as a build or a virtual environment, are never listed.
    listed = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.py"],
        cwd=root,
        capture_output=True,
        check=True,
        text=True,
    ).stdout
    # A tracked file deleted from the working tree stays in the index until its deletion is staged.
    paths = sorted({Path(name) for name in listed.split("\0") if name})
    return [path for path in paths if (root / path).is_file()]


def uses(text: str) -> list[tuple[int, str, str | None, bool]]:
    """Each use of a pytest exception matcher: line, form, function, and whether it is bare."""
    tree = ast.parse(text)
    aliases = {"pytest"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            aliases |= {name.asname or name.name for name in node.names if name.name == "pytest"}
    found = []

    def visit(node: ast.AST, function: str | None) -> None:
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef):
            function = node.name
        if isinstance(node, ast.ImportFrom) and node.module == "pytest":
            for name in node.names:
                if name.name in MATCHERS or name.name == "*":
                    found.append((node.lineno, f"imports {name.name} from pytest", None, False))
        elif isinstance(node, ast.Call) and _is_matcher(node.func, aliases):
            bare = len(node.args) == 1 and not node.keywords
            found.append((node.lineno, f"calls {ast.unparse(node.func)}", function, bare))
            for child in [*node.args, *node.keywords]:
                visit(child, function)
            return
        elif _is_matcher(node, aliases):
            found.append((node.lineno, f"uses {ast.unparse(node)}", None, False))
        for child in ast.iter_child_nodes(node):
            visit(child, function)

    visit(tree, None)
    return sorted(found)


def helper_uses(text: str) -> list[tuple[int, str]]:
    """Each definition or import of a helper name outside the helper, and each bad template."""
    found = []
    for node in ast.walk(ast.parse(text)):
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef) and node.name in HELPERS:
            found.append((node.lineno, f"defines {node.name}; import it from {HELPER.stem}"))
        elif isinstance(node, ast.ImportFrom) and node.module not in (HELPER.stem, "pytest"):
            for name in node.names:
                if name.name in HELPERS:
                    found.append((node.lineno, f"imports {name.name} from {node.module}"))
        elif isinstance(node, ast.Call) and _called_name(node) == "raises_shape":
            template = node.args[1] if len(node.args) == 2 else None
            if template is None or not _template_is_safe(template):
                found.append((node.lineno, "gives raises_shape a template beyond text and {n}"))
    return sorted(found)


def _called_name(node: ast.Call) -> str | None:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None


def _template_is_safe(node: ast.expr) -> bool:
    """Whether the literal text of a template has no alternation, wildcard, brace or backslash."""
    if isinstance(node, ast.Constant):
        parts = [node.value] if isinstance(node.value, str) else []
    elif isinstance(node, ast.JoinedStr):
        parts = [
            v.value for v in node.values if isinstance(v, ast.Constant) and isinstance(v.value, str)
        ]
    else:
        # A template built elsewhere: the helper itself rejects the same text when it runs.
        return True
    return not any(bad in part.replace(NUMBER, "") for part in parts for bad in NOT_IN_TEMPLATE)


def _is_matcher(node: ast.AST, aliases: set[str]) -> TypeGuard[ast.Attribute]:
    return (
        isinstance(node, ast.Attribute)
        and node.attr in MATCHERS
        and isinstance(node.value, ast.Name)
        and node.value.id in aliases
    )


def check(root: Path) -> list[str]:
    """Each use of a pytest exception matcher outside the helper module and the allowlist."""
    allowed, problems = read_allowlist(root)
    used = set()
    for path in python_files(root):
        if path == HELPER:
            continue
        for line, what, function, bare in uses((root / path).read_text(encoding="utf-8")):
            key = (path.as_posix(), function or "")
            if key in allowed and bare:
                used.add(key)
                continue
            problems.append(
                f"{path}:{line}: {what}; expect an exception with raises() of {HELPER.name}"
            )
        for line, what in helper_uses((root / path).read_text(encoding="utf-8")):
            problems.append(f"{path}:{line}: {what}")
    for path, function in sorted(set(allowed) - used):
        problems.append(
            f"{ALLOWLIST}: {path} {function} has no bare pytest.raises call; remove the entry"
        )
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
