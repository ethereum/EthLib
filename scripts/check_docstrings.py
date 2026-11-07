"""Check that every Python module docstring is one line, and that no docstring wraps a sentence."""

import ast
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The key generator is pinned by its digest in `tests/consensus/pq_keys/SHA256SUMS`.
EXCLUDED = {Path("tests/consensus/pq_keys/generate.py")}

# A line that ends a sentence, or introduces a list or a block.
END = (".", ":", "!", "?")
# A line that starts a list item.
ITEM = re.compile(r"(?:[-*+]|\d+[.)])\s")
# A line that holds only a URL.
URL = re.compile(r"<?https?://\S+>?")
# A line that opens or closes a fenced block.
FENCE = re.compile(r"(```|~~~)")


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
    return [path for path in paths if (root / path).is_file() and path not in EXCLUDED]


def wrapped_lines(docstring: str) -> list[int]:
    """The offsets, from the first line, of each line that continues the sentence above it."""
    lines = docstring.split("\n")
    # The indentation of the body: the least of every non-blank line after the first.
    rest = [line for line in lines[1:] if line.strip()]
    base = min((len(line) - len(line.lstrip(" ")) for line in rest), default=0)
    found = []
    in_fence = False
    previous = None
    for offset, line in enumerate(lines):
        stripped = line.strip()
        if FENCE.match(stripped):
            in_fence = not in_fence
            previous = None
            continue
        # Code, a doctest, a table row and a URL alone are not prose.
        code = in_fence or (offset > 0 and len(line) - len(line.lstrip(" ")) >= base + 4)
        if not stripped or code or stripped.startswith((">>>", "|")) or URL.fullmatch(stripped):
            previous = None
            continue
        if previous is not None and not previous.endswith(END) and not ITEM.match(stripped):
            found.append(offset)
        previous = stripped
    return found


def check_text(path: str, text: str) -> list[str]:
    """Each docstring problem of one Python file."""
    tree = ast.parse(text)
    problems = []
    module = ast.get_docstring(tree, clean=False)
    if module is not None and "\n" in module:
        problems.append(f"{path}:1: the module docstring has more than one line")
    for node in ast.walk(tree):
        if not isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef):
            continue
        docstring = ast.get_docstring(node, clean=False)
        if docstring is None:
            continue
        # The first statement of the body is the docstring, and its first line holds the quotes.
        first = node.body[0].lineno
        for offset in wrapped_lines(docstring):
            problems.append(
                f"{path}:{first + offset}: a sentence of the docstring of {node.name} "
                "wraps onto this line"
            )
    return problems


def check(root: Path) -> list[str]:
    """Each docstring problem of the Python files under the root."""
    problems = []
    for path in python_files(root):
        problems += check_text(path.as_posix(), (root / path).read_text(encoding="utf-8"))
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
