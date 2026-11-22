"""Check that no Lean comment quotes code, a source's names or emphasis, or the Python specs."""

import re
import sys
from collections.abc import Callable, Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST = Path("scripts/check_comment_code_allowlist.txt")

# A span between backticks, on one line.
SPAN = re.compile(r"`([^`\n]+)`")
COMPARISON = re.compile(r"==|!=|<=|>=|(?<![-<])<(?![-=])|(?<![-=])>(?!=)")
BOOLEAN_WORD = re.compile(r"\b(?:and|or|not)\b")
# A whole span that is a snake_case name of a source, such as `storage_changes` or `get_code()`.
SNAKE_NAME = re.compile(r"[a-z]{2,}(?:_[a-z]{2,})+(?:\.[a-z_]+)*(?:\(.*\))?")
# A snake_case name inside a longer span, such as `current_target = tx.to`.
SNAKE_TOKEN = re.compile(r"\b[a-z]{2,}(?:_[a-z]{2,})+\b")
CODE_SYNTAX = re.compile(r"[=(\[]|\w\.\w")
# A Lean declaration, whose last name component a comment may write, as for a theorem.
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|public|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([\w.']+)",
    re.M,
)
# A character literal, such as `'a'` or `'\''`.
CHAR = re.compile(r"'(?:\\.|[^\\'\n])'")
# The opening of a raw string, such as `r"` or `r#"`.
RAW_OPEN = re.compile(r'r(#*)"')

Scope = Literal["span", "line", "prose"]


@dataclass(frozen=True, kw_only=True)
class Rule:
    """One kind of code in a comment: its code, what it reads, its test and its advice."""

    code: str
    # What the rule reads: each span between backticks, the whole line, or the line without spans.
    scope: Scope
    # Whether the rule skips doc comments, for prose that a doc comment may hold.
    skip_doc: bool = False
    # Whether the rule skips the proofs, whose comments name the lemmas they use.
    skip_proofs: bool = False
    # Whether the text breaks the rule, given the names that EthLib declares.
    breaks: Callable[[str, frozenset[str]], bool]
    advice: str


def pattern(regex: str) -> Callable[[str, frozenset[str]], bool]:
    """A test that holds when the regular expression occurs in the text."""
    compiled = re.compile(regex)
    return lambda text, _: compiled.search(text) is not None


def joined_comparison(span: str, _: frozenset[str]) -> bool:
    """Whether a span joins a comparison with `and`, `or` or `not`, as a condition of code does."""
    return COMPARISON.search(span) is not None and BOOLEAN_WORD.search(span) is not None


def source_name(span: str, declared: frozenset[str]) -> bool:
    """Whether a whole span is a snake_case name that EthLib does not declare."""
    return SNAKE_NAME.fullmatch(span) is not None and span not in declared


def code_with_name(span: str, declared: frozenset[str]) -> bool:
    """Whether a span mixes a snake_case name of a source with the syntax of code."""
    names = set(SNAKE_TOKEN.findall(span)) - declared
    return bool(names) and CODE_SYNTAX.search(span) is not None and not SNAKE_NAME.fullmatch(span)


RULES = (
    Rule(
        code="C1",
        scope="span",
        breaks=pattern(r"==|!="),
        advice="write `=` or `≠` in words",
    ),
    Rule(
        code="C2",
        scope="line",
        breaks=pattern(r"\bfor\s+\w+(?:\s*,\s*\w+)*\s+in\s+[\w.\[\]()]+\s*:"),
        advice="state the loop in words, such as `each x of y`",
    ),
    Rule(
        code="C3",
        scope="span",
        breaks=pattern(r"^\s*(?:el)?if\b.*:\s*$|^\s*else:"),
        advice="state the condition in words",
    ),
    Rule(
        code="C4",
        scope="span",
        breaks=pattern(r"\bassert\s+\S"),
        advice="state what must hold",
    ),
    Rule(
        code="C5",
        scope="span",
        breaks=pattern(r"\breturn\b"),
        advice="say what the step gives",
    ),
    Rule(
        code="C6",
        scope="line",
        breaks=pattern(r"\bdef\s+\w+\s*\("),
        advice="name the step, not a function",
    ),
    Rule(
        code="C7",
        scope="line",
        breaks=pattern(r"\.append\(|\blen\("),
        advice="say the count in words",
    ),
    Rule(
        code="C8",
        scope="line",
        breaks=pattern(r"\w\*\*\w|\w\s+\*\*\s+\w"),
        advice="write `a^b` for a power",
    ),
    Rule(
        code="C9",
        scope="span",
        breaks=pattern(r"(?<![:/])//(?!/)"),
        advice="write `floor(a / b)`",
    ),
    Rule(
        code="C10",
        scope="span",
        breaks=joined_comparison,
        advice="write the conditions in words, one by one",
    ),
    Rule(
        code="C11",
        scope="line",
        skip_doc=True,
        breaks=pattern(r"^\s*[a-z]{2,}(?:_[a-z]{2,})+\s*:"),
        advice="name the step in words, not after a function of a source",
    ),
    Rule(
        code="C12",
        scope="line",
        breaks=pattern(r"(?i)\b(?:execution|consensus)[-_ ]specs\b|\bpyspec\b"),
        advice="state the rule in EthLib's terms; the pins belong to the test suites",
    ),
    Rule(
        code="C13",
        scope="span",
        skip_doc=True,
        skip_proofs=True,
        breaks=source_name,
        advice="name the thing in plain words, not by a source's identifier",
    ),
    Rule(
        code="C14",
        scope="prose",
        skip_doc=True,
        breaks=pattern(r"(?<!\w)\*\*[^\s*][^*]*\*\*"),
        advice="write the words without Markdown emphasis",
    ),
    Rule(
        code="C15",
        scope="span",
        skip_doc=True,
        skip_proofs=True,
        breaks=code_with_name,
        advice="state the step in words or in the notation of its source",
    ),
)


@dataclass(frozen=True)
class Comment:
    """One line of a Lean comment: its line number, its kind and its text."""

    line: int
    doc: bool
    text: str


def comments(source: str) -> Iterator[Comment]:
    """The lines of the comments of a Lean file, outside string and character literals."""
    depth, doc, line, index = 0, False, 1, 0
    current: list[str] = []
    size = len(source)
    while index < size:
        char = source[index]
        pair = source[index : index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                current.append(pair)
                index += 2
            elif pair == "-/":
                depth -= 1
                if depth == 0:
                    yield Comment(line, doc, "".join(current))
                    current = []
                else:
                    current.append(pair)
                index += 2
            elif char == "\n":
                yield Comment(line, doc, "".join(current))
                current = []
                line += 1
                index += 1
            else:
                current.append(char)
                index += 1
            continue
        if pair == "--":
            end = source.find("\n", index)
            end = size if end < 0 else end
            yield Comment(line, False, source[index + 2 : end])
            index = end
            continue
        if pair == "/-":
            depth, doc = 1, source[index + 2 : index + 3] in ("-", "!")
            index += 3 if doc else 2
            continue
        identifier_before = index > 0 and (source[index - 1].isalnum() or source[index - 1] in "_'")
        raw = None if identifier_before else RAW_OPEN.match(source, index)
        if raw:
            close = '"' + raw.group(1)
            end = source.find(close, raw.end())
            end = size if end < 0 else end + len(close)
            line += source.count("\n", index, end)
            index = end
            continue
        if char == '"':
            index += 1
            while index < size and source[index] != '"':
                # An escape skips its next character, which can be the newline of a string gap.
                step = 2 if source[index] == "\\" else 1
                line += source.count("\n", index, index + step)
                index += step
            index += 1
            continue
        if char == "'" and not identifier_before and (literal := CHAR.match(source, index)):
            index = literal.end()
            continue
        if char == "\n":
            line += 1
        index += 1


@dataclass(frozen=True)
class Finding:
    """A rule that a comment line breaks, with the span or line it read."""

    code: str
    text: str
    advice: str


def findings(comment: Comment, *, proof: bool, declared: frozenset[str]) -> Iterator[Finding]:
    """Each rule that each span or line of a comment breaks."""
    spans = [span.strip() for span in SPAN.findall(comment.text)]
    texts: dict[Scope, list[str]] = {
        "span": spans,
        "line": [comment.text.strip()],
        "prose": [SPAN.sub("", comment.text).strip()],
    }
    for rule in RULES:
        if (rule.skip_doc and comment.doc) or (rule.skip_proofs and proof):
            continue
        for text in texts[rule.scope]:
            if rule.breaks(text, declared):
                yield Finding(rule.code, text, rule.advice)


def read_allowlist(root: Path) -> tuple[dict[tuple[str, str, str], str], list[str]]:
    """The allowed findings, each keyed by file, rule and text, and the malformed lines."""
    entries: dict[tuple[str, str, str], str] = {}
    problems: list[str] = []
    path = root / ALLOWLIST
    if not path.exists():
        return entries, problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        # The text comes last, since a concatenation in it can hold ` | ` too.
        parts = [part.strip() for part in line.split(" | ", 3)]
        if len(parts) != 4 or not all(parts):
            problems.append(f"{ALLOWLIST}:{number}: an entry is `path | rule | reason | text`")
            continue
        key = (parts[0], parts[1], parts[3])
        if key in entries:
            problems.append(f"{ALLOWLIST}:{number}: the entry repeats an earlier one")
            continue
        entries[key] = parts[2]
    return entries, problems


def check(root: Path) -> list[str]:
    """Every comment that quotes code, and every stale or malformed entry of the allowlist."""
    allowed, problems = read_allowlist(root)
    used: set[tuple[str, str, str]] = set()
    sources = {
        file.relative_to(root).as_posix(): file.read_text(encoding="utf-8")
        for file in sorted((root / "EthLib").rglob("*.lean"))
    }
    declared = frozenset(
        name.rsplit(".", 1)[-1] for text in sources.values() for name in DECLARATION.findall(text)
    )
    for relative, text in sources.items():
        proof = "Proofs" in relative.split("/")
        for comment in comments(text):
            # A text is reported once, for the first rule that it breaks without an entry.
            reported: set[str] = set()
            for finding in findings(comment, proof=proof, declared=declared):
                # One entry covers every copy of its text in its file.
                key = (relative, finding.code, finding.text)
                if key in allowed:
                    used.add(key)
                elif finding.text not in reported:
                    reported.add(finding.text)
                    where = f"{relative}:{comment.line}"
                    problems.append(f"{where}: {finding.code} {finding.advice}: {finding.text}")
    for path, code, text in sorted(set(allowed) - used):
        problems.append(f"{ALLOWLIST}: the entry {path} | {code} | {text} matches nothing")
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
