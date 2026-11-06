"""Check the line length and the comment layout of the Lean lines that a branch changes."""

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from itertools import pairwise
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The Mathlib limit on the length of a line.
MAX_LENGTH = 100

# A URL alone, or a Markdown link reference definition `[label]: URL`.
URL = r"\s*(?:\[[^\]\n]+\]:\s*)?<?https?://\S+?>?\s*"
URL_CONTENT = re.compile(URL)
# A line that holds only a URL, optionally after a comment opener or before a closer.
URL_LINE = re.compile(r"\s*(?:--|/--|/-!|/-)?" + URL + r"(?:-/)?\s*")

RAW_STRING = re.compile(r'r(#*)"')
CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|.)|[^\\'\n])'")
LIST_ITEM = re.compile(r"(?:[-*+]|\d+[.)])(?:\s|$)")
FENCE = re.compile(r"(```|~~~)")


@dataclass(frozen=True)
class Finding:
    """A layout finding at a line of a file."""

    path: str
    line: int
    message: str


def is_ident(char: str) -> bool:
    """Whether a character can continue a Lean identifier."""
    return char.isalnum() or char in "_'!?"


def comments(text: str) -> list[list[tuple[int, str]]]:
    """
    The comments of a Lean file, each as a list of (line number, content) pairs.

    A block comment `/- … -/`, `/-- … -/` or `/-! … -/` is one comment, without its markers.
    Block comments nest.

    Line comments `--` on consecutive lines, each alone on its line, form one comment.
    A line comment after code is a comment of its own.

    Strings, raw strings and character literals are skipped, so a `--` inside them is not a comment.
    """
    found: list[list[tuple[int, str]]] = []
    run: list[tuple[int, str]] = []
    index, line, length = 0, 1, len(text)

    def flush() -> None:
        if run:
            found.append(run.copy())
            run.clear()

    while index < length:
        char = text[index]
        if char == "\n":
            line += 1
            index += 1
            continue
        if text.startswith("/-", index):
            flush()
            opener = 3 if text.startswith(("/--", "/-!"), index) else 2
            cursor, depth = index + 2, 1
            while cursor < length and depth:
                if text.startswith("/-", cursor):
                    depth, cursor = depth + 1, cursor + 2
                elif text.startswith("-/", cursor):
                    depth, cursor = depth - 1, cursor + 2
                else:
                    cursor += 1
            body = text[index + opener : cursor - 2 if depth == 0 else cursor]
            found.append([(line + k, part) for k, part in enumerate(body.split("\n"))])
            line += text.count("\n", index, cursor)
            index = cursor
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            end = length if end < 0 else end
            content = text[index + 2 : end]
            if text[text.rfind("\n", 0, index) + 1 : index].strip():
                flush()
                found.append([(line, content)])
            else:
                if run and run[-1][0] != line - 1:
                    flush()
                run.append((line, content))
            index = end
            continue
        if char.isspace():
            index += 1
            continue
        if run and run[-1][0] != line:
            flush()
        previous = text[index - 1] if index else ""
        raw = RAW_STRING.match(text, index)
        if raw and not is_ident(previous):
            close = '"' + raw.group(1)
            end = text.find(close, raw.end())
            end = length if end < 0 else end + len(close)
        elif char == '"':
            end = index + 1
            while end < length and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            end = min(end + 1, length)
        elif (
            char == "'" and not is_ident(previous) and (literal := CHAR_LITERAL.match(text, index))
        ):
            end = literal.end()
        else:
            index += 1
            continue
        line += text.count("\n", index, end)
        index = end
    flush()
    return found


def indentation(content: str) -> int:
    """The number of spaces at the start of a line."""
    return len(content) - len(content.lstrip(" "))


def sentence_lines(comment: list[tuple[int, str]]) -> list[tuple[int, bool]]:
    """
    Each line of a comment, with whether it is a sentence line.

    A sentence line holds a letter or a digit.
    It is not a heading, a table row, a URL alone or a link reference definition.
    It is not a list item or its continuation, and not a line of a fenced or an indented code block.

    Indented code is indented by four spaces more than the least indented line after the first.
    """
    rest = [content for _, content in comment[1:] if content.strip()]
    base = min(map(indentation, rest), default=0)
    out = []
    in_fence = in_list = False
    for number, content in comment:
        stripped = content.strip()
        if FENCE.match(stripped):
            in_fence = not in_fence
            out.append((number, False))
            continue
        if not stripped:
            in_list = False
        elif LIST_ITEM.match(stripped):
            in_list = True
        code = in_fence or (number != comment[0][0] and indentation(content) >= base + 4)
        sentence = (
            bool(stripped)
            and not code
            and not in_list
            and not stripped.startswith(("#", "|"))
            and not URL_CONTENT.fullmatch(content)
            and any(c.isalnum() for c in stripped)
        )
        out.append((number, sentence))
    return out


def check_text(path: str, text: str, changed: set[int] | None) -> list[Finding]:
    """The findings on the changed lines of one Lean file; `None` means every line changed."""

    def is_changed(number: int) -> bool:
        return changed is None or number in changed

    found = []
    for number, content in enumerate(text.split("\n"), start=1):
        if is_changed(number) and len(content) > MAX_LENGTH and not URL_LINE.fullmatch(content):
            found.append(
                Finding(path, number, f"line has {len(content)} characters, more than {MAX_LENGTH}")
            )
    # Two sentence lines that touch fail when the branch changes at least one of them.
    for comment in comments(text):
        lines = sentence_lines(comment)
        for (first, first_sentence), (second, second_sentence) in pairwise(lines):
            if first_sentence and second_sentence and (is_changed(first) or is_changed(second)):
                found.append(
                    Finding(
                        path,
                        second,
                        "comment has two sentence lines in a row; put a blank line between them",
                    )
                )
    return sorted(found, key=lambda f: f.line)


def git(*args: str) -> str:
    """The standard output of a git command run at the root of the repository."""
    return subprocess.run(
        ["git", *args], check=True, capture_output=True, text=True, cwd=ROOT
    ).stdout


def changed_lines(base: str) -> dict[str, set[int]]:
    """Map each Lean file that the branch adds or changes to the line numbers that it adds."""
    merge_base = git("merge-base", base, "HEAD").strip()
    diff = git("diff", "--unified=0", "--no-color", "--no-ext-diff", merge_base, "--", "*.lean")
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
    return result


def main(argv: list[str]) -> int:
    """Print the layout findings of the files, and return the exit code."""
    parser = argparse.ArgumentParser(description=__doc__.strip().split("\n")[0])
    parser.add_argument("--base", help="check the lines changed since the merge base with BASE")
    parser.add_argument("files", nargs="*", help="check every line of these files")
    parser.add_argument("--github", action="store_true", help="print GitHub annotations")
    args = parser.parse_args(argv[1:])
    if bool(args.base) == bool(args.files):
        parser.error("give either --base or at least one file")
    if args.base:
        targets = [(path, lines) for path, lines in sorted(changed_lines(args.base).items())]
        root = ROOT
    else:
        targets = [(name, None) for name in args.files]
        root = Path.cwd()
    found = []
    for path, lines in targets:
        found += check_text(path, (root / path).read_text(encoding="utf-8"), lines)
    for item in found:
        if args.github:
            print(f"::error file={item.path},line={item.line},title=Lean layout::{item.message}")
        else:
            print(f"{item.path}:{item.line}: {item.message}")
    print(f"{len(found)} layout finding(s)." if found else "No layout findings.")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
