"""Check that no sentence of a Python comment runs onto a second line."""

import argparse
import io
import re
import subprocess
import sys
import tokenize
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The key generator is pinned by its digest in `tests/consensus/pq_keys/SHA256SUMS`.
EXCLUDED = {"tests/consensus/pq_keys/generate.py"}

# A line that starts a list item.
LIST_ITEM = re.compile(r"(?:[-*+]|\d+[.)])(?:\s|$)")
# A line of a provenance record, such as `Commit: <hash>`, which is a field and not a sentence.
RECORD = re.compile(
    r"(?:Files?|File sha256|Directory|Repository|Commit|Release|Section|Source|Licen[cs]e"
    r"|SPDX-License-Identifier):\s"
)
# A line that opens or closes a fenced block.
FENCE = re.compile(r"(```|~~~)")
# A URL alone, or a Markdown link reference definition `[label]: URL`.
URL = re.compile(r"(?:\[[^\]\n]+\]:\s*)?<?https?://\S+?>?")
# The end of a sentence: a full stop, a question mark, an exclamation mark or a colon.
# Closing brackets, quotes or emphasis may follow it.
SENTENCE_END = re.compile(r"[.?!:][)\]\"'`*_]*$")


@dataclass(frozen=True)
class Finding:
    """A wrapped sentence at a line of a file."""

    path: str
    line: int


def comments(text: str) -> list[list[tuple[int, str]]]:
    """
    The comments of a Python file, each as a list of (line number, text after the hash) pairs.

    Comments alone on consecutive lines, at the same column, form one comment.
    A comment after code is a comment of its own.
    """
    found: list[list[tuple[int, str]]] = []
    run: list[tuple[int, str]] = []
    column = -1
    lines = text.split("\n")
    for token in tokenize.generate_tokens(io.StringIO(text).readline):
        if token.type != tokenize.COMMENT:
            continue
        number, start = token.start
        content = token.string[1:]
        if lines[number - 1][:start].strip():
            found.append([(number, content)])
            continue
        if run and (run[-1][0] != number - 1 or column != start):
            found.append(run)
            run = []
        run.append((number, content))
        column = start
    if run:
        found.append(run)
    return found


def indentation(content: str) -> int:
    """The number of spaces at the start of a line."""
    return len(content) - len(content.lstrip(" "))


def wrapped_lines(comment: list[tuple[int, str]]) -> list[int]:
    """
    Each line of a comment that continues a sentence of the line above it.

    The line above is prose that does not end a sentence.
    Prose is any line with a letter or a digit that is not a heading, a table row or a URL alone.
    A field of a provenance record is not prose either.

    A blank line, a fenced or indented code block, and a line that is not prose end a paragraph.
    A new list item continues nothing.
    Indented code is indented by four spaces more than the least indented line.
    """
    rest = [content for _, content in comment if content.strip()]
    base = min(map(indentation, rest), default=0)
    out = []
    in_fence = False
    # The previous prose line of the paragraph, when it does not end a sentence.
    open_line = False
    for number, content in comment:
        stripped = content.strip()
        if FENCE.match(stripped):
            in_fence = not in_fence
            open_line = False
            continue
        code = in_fence or indentation(content) >= base + 4
        prose = (
            bool(stripped)
            and not code
            and not stripped.startswith(("#", "|", "!"))
            and not URL.fullmatch(stripped)
            and not RECORD.match(stripped)
            and any(c.isalnum() for c in stripped)
        )
        if not prose:
            open_line = False
            continue
        if open_line and not LIST_ITEM.match(stripped):
            out.append(number)
        open_line = not SENTENCE_END.search(stripped)
    return out


def check_text(path: str, text: str, changed: set[int] | None) -> list[Finding]:
    """
    The wrapped sentences of one Python file that touch a changed line.

    With no set of changed lines, every line counts as changed.
    """
    found = []
    for comment in comments(text):
        numbers = [number for number, _ in comment]
        for number in wrapped_lines(comment):
            # A pair of lines fails when the branch changes at least one of them.
            previous = numbers[numbers.index(number) - 1]
            if changed is None or number in changed or previous in changed:
                found.append(Finding(path, number))
    return found


def git(*args: str) -> str:
    """The standard output of a git command run at the root of the repository."""
    return subprocess.run(
        ["git", *args], check=True, capture_output=True, text=True, cwd=ROOT
    ).stdout


def changed_lines(base: str) -> dict[str, set[int]]:
    """Map each Python file that the branch adds or changes to the line numbers that it adds."""
    merge_base = git("merge-base", base, "HEAD").strip()
    diff = git("diff", "--unified=0", "--no-color", "--no-ext-diff", merge_base, "--", "*.py")
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
    # `git diff` lists no untracked file, so every line of a new file that is not yet added counts.
    untracked = git("ls-files", "-z", "--others", "--exclude-standard", "--", "*.py")
    for path in filter(None, untracked.split("\0")):
        count = len((ROOT / path).read_text(encoding="utf-8").splitlines())
        result[path] = set(range(1, count + 1))
    return result


def main(argv: list[str]) -> int:
    """Print each wrapped sentence of the files, and return the exit code."""
    parser = argparse.ArgumentParser(description=__doc__.strip())
    parser.add_argument("--base", help="check the lines changed since the merge base with BASE")
    parser.add_argument("--all", action="store_true", help="check every tracked Python file")
    parser.add_argument("files", nargs="*", help="check every line of these files")
    parser.add_argument("--github", action="store_true", help="print GitHub annotations")
    args = parser.parse_args(argv[1:])
    if sum((bool(args.base), bool(args.files), args.all)) != 1:
        parser.error("give one of --base, --all or at least one file")
    if args.base:
        targets = sorted(changed_lines(args.base).items())
        root = ROOT
    elif args.all:
        tracked = git("ls-files", "-z", "--", "*.py")
        targets = [(path, None) for path in sorted(filter(None, tracked.split("\0")))]
        root = ROOT
    else:
        targets = [(name, None) for name in args.files]
        root = Path.cwd()
    found = []
    for path, lines in targets:
        if path in EXCLUDED or not (root / path).is_file():
            continue
        found += check_text(path, (root / path).read_text(encoding="utf-8"), lines)
    message = "sentence runs onto this line; give each sentence a line of its own"
    for item in found:
        if args.github:
            print(f"::error file={item.path},line={item.line},title=Python comment::{message}")
        else:
            print(f"{item.path}:{item.line}: {message}")
    print(f"{len(found)} wrapped comment line(s)." if found else "No wrapped comment lines.")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
