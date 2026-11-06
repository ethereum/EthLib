"""Check that every C export which reads a fork name rejects the forks whose rules it lacks."""

import importlib.util
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Load the comment stripper of `soundness_facts.py` by path: `scripts` is not a package.
_spec = importlib.util.spec_from_file_location(
    "soundness_facts", Path(__file__).resolve().parent / "soundness_facts.py"
)
assert _spec and _spec.loader
_facts = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_facts)
strip_lean = _facts.strip_lean

# The module that defines the two readers of a fork name.
READERS = Path("EthLib/Base/Exports.lean")
ALLOWLIST = Path("scripts/check_fork_cap_allowlist.txt")

CAPPED = re.compile(r"\bforkUpTo\b")
UNCAPPED = re.compile(r"\bforkOfName\b|\bFork\.ofName\?")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|public)\s+)*"
    r"(?:def|abbrev|theorem|instance|opaque)\b\s*([^\s(:{\[]*)",
    re.M,
)
ATTRIBUTE = re.compile(r"^@\[([^\]]*)\]", re.M)
BLOCK_END = re.compile(r"^(?:end|namespace|section|open|variable|@\[)\b", re.M)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
FORK_BINDER = re.compile(r"[({]([^(){}:]*):")


@dataclass
class Decl:
    """A top-level Lean definition, with its header, its body and its export attribute."""

    path: str
    name: str
    header: str
    body: str
    export: bool


def declarations(path: str, text: str) -> list[Decl]:
    """The top-level definitions of a Lean file, each with its header and its body."""
    code = strip_lean(text)
    starts = list(DECL.finditer(code))
    found = []
    for index, match in enumerate(starts):
        stop = starts[index + 1].start() if index + 1 < len(starts) else len(code)
        if end := BLOCK_END.search(code, match.end(), stop):
            stop = end.start()
        attributes = " ".join(ATTRIBUTE.findall(code[match.start() : match.end()]))
        body = code[match.end() : stop]
        header = re.split(r":=|\bwhere\b", body, maxsplit=1)[0]
        name = match.group(1).split(".")[-1]
        export = re.search(r"\bexport\b", attributes) is not None
        found.append(Decl(path, name, header, body, export))
    return found


def takes_fork(decl: Decl) -> bool:
    """Whether a binder of the declaration names a fork."""
    return any(
        "fork" in name.lower()
        for names in FORK_BINDER.findall(decl.header)
        for name in names.split()
    )


def read_allowlist(path: Path) -> tuple[dict[tuple[str, str], str], list[str]]:
    """The allowlisted definitions, each with its reason, and the malformed lines."""
    entries, problems = {}, []
    if not path.exists():
        return entries, problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        match = re.fullmatch(r"(\S+)\s+(\S+):\s*(.*\S)?\s*", line)
        if not match or not match.group(3):
            problems.append(f"{path}:{number}: an entry is `path name: reason`, on one line")
            continue
        entries[(match.group(1), match.group(2))] = match.group(3)
    return entries, problems


def check(root: Path) -> list[str]:
    """Every problem with the fork caps of the exports and with the allowlist."""
    allowed, problems = read_allowlist(root / ALLOWLIST)
    decls = []
    for file in sorted((root / "EthLib").rglob("*.lean")):
        relative = file.relative_to(root)
        if relative == READERS or "Proofs" in relative.parts:
            continue
        decls += declarations(relative.as_posix(), file.read_text(encoding="utf-8"))
    by_name: dict[str, list[Decl]] = {}
    for decl in decls:
        by_name.setdefault(decl.name, []).append(decl)
    used = set()
    for decl in decls:
        if UNCAPPED.search(decl.body):
            key = (decl.path, decl.name)
            if key in allowed:
                used.add(key)
            else:
                problems.append(
                    f"{decl.path}: {decl.name} reads a fork name without a cap; "
                    "use forkUpTo, or list it in the allowlist with a reason"
                )

    def capped(start: Decl) -> bool:
        seen, todo = set(), [start]
        while todo:
            decl = todo.pop()
            if id(decl) in seen:
                continue
            seen.add(id(decl))
            if CAPPED.search(decl.body) or (decl.path, decl.name) in allowed:
                return True
            for ident in IDENT.findall(decl.body):
                todo += by_name.get(ident.split(".")[-1], [])
        return False

    for decl in decls:
        if decl.export and takes_fork(decl) and not capped(decl):
            problems.append(
                f"{decl.path}: export {decl.name} takes a fork but never caps it with forkUpTo"
            )
    for path, name in sorted(set(allowed) - used):
        problems.append(f"{ALLOWLIST}: {path} {name} reads no fork name; remove the entry")
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
