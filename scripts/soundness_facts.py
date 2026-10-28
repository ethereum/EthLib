"""
Keep the facts in SOUNDNESS.md that the repository can state for itself.

SOUNDNESS.md has two kinds of content.

The prose is reviewed by hand, for one package version: the document names
the version in `pyproject.toml`, and this script fails when that version
changes, so every version bump reviews the document again. The script never
edits that line.

The facts that change with the code, such as the theorems that still use
`native_decide`, are generated between markers:

    <!-- generated: NAME -->
    ...
    <!-- end generated -->

    python3 scripts/soundness_facts.py           # rewrite the generated blocks
    python3 scripts/soundness_facts.py --check   # fail if any is out of date, or the version differs

Only the standard library is used, and Python 3.10 is enough, so the check
needs no Lean, no build and no install step.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

BLOCK = re.compile(r"(<!-- generated: (\S+) -->\n)(.*?)(<!-- end generated -->)", re.S)
VERSION_LINE = re.compile(
    r"^This document describes the development tree that declares package version `([^`]+)` in `pyproject.toml`\.$",
    re.M)


def baseline(root: Path) -> list[tuple[str, str]]:
    """The declaration-check baseline, as (kind, declaration) pairs.

    `lake exe check-decls` fails on a stale entry as well as on a missing
    one, so in a tree that passes CI the baseline is the exact list of
    findings."""
    out = []
    for line in (root / "scripts" / "check_decls_baseline.txt").read_text().splitlines():
        fields = line.split("#", 1)[0].split()
        if len(fields) == 2:
            out.append((fields[0], fields[1]))
    return out


def readable(decl: str) -> str:
    """A declaration name as a reader would write it.
    A private name, `_private.<module>.0.<name>`, becomes `<name>` marked private."""
    if decl.startswith("_private."):
        return f"`{decl.split('.0.', 1)[1]}` (private)"
    return f"`{decl}`"


def native(root: Path) -> str:
    names = sorted((d for k, d in baseline(root) if k == "native"), key=readable)
    if not names:
        return "No theorem uses them.\n"
    return (f"{len(names)} theorems still use them, and "
            "`scripts/check_decls_baseline.txt` lists each one:\n\n"
            + "".join(f"- {readable(n)}\n" for n in names))


def unfoldable(root: Path) -> str:
    found = sorted((d, k) for k, d in baseline(root) if k in ("partial", "opaque", "reaches-opaque"))
    return "".join(f"- {readable(d)}, `{k}`\n" for d, k in found)


def blank(text: str) -> str:
    """`text` with every character but newlines replaced by a space, so lines stay where they were."""
    return re.sub(r"[^\n]", " ", text)


def is_ident(c: str) -> bool:
    return c.isalnum() or c in "_'!?"


def strip_lean(text: str) -> str:
    """Lean source with its comments and string and character literals blanked out.

    Block comments `/- … -/` nest, so a depth is kept; a line comment runs from
    `--` to the end of the line. A string `"…"` honours backslash escapes, and a
    raw string `r#"…"#` ends at the quote followed by as many `#` as it opened
    with. A character literal is `'c'` or an escape such as `'\\n'`, where the `'` does not end an
    identifier such as `x'`."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            j, depth = i + 2, 1
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
        elif (m := re.compile(r'r(#*)"').match(text, i)) and (i == 0 or not is_ident(text[i - 1])):
            close = '"' + m.group(1)
            j = text.find(close, m.end())
            j = n if j < 0 else j + len(close)
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
        elif (m := re.compile(r"'(\\.[^']*|[^\\'])'").match(text, i)) and (i == 0 or not is_ident(text[i - 1])):
            j = m.end()
        else:
            out.append(text[i])
            i += 1
            continue
        out.append(blank(text[i:j]))
        i = j
    return "".join(out)


def lean_exports(root: Path) -> set[str]:
    """Every `@[export name]` symbol in an export module.

    An attribute list may span lines and hold other attributes, as in
    `@[inline,\\n  export eth_foo]`, and `attribute [export eth_foo] decl` is
    the other way to write one."""
    symbols = set()
    for path in (root / "EthLib").rglob("*.lean"):
        if "Exports" not in path.parts:
            continue
        text = strip_lean(path.read_text())
        for attrs in re.findall(r"(?:@|\battribute\s*)\[([^\]]*)\]", text):
            symbols |= set(re.findall(r"\bexport\s+(\w+)", attrs))
    return symbols


def strip_c(text: str) -> str:
    """C source with its comments and string and character literals blanked out.

    Block comments `/* … */` do not nest in C. A string `"…"` and a character
    `'…'` honour backslash escapes."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
        elif text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
        elif text[i] in "\"'":
            quote, j = text[i], i + 1
            while j < n and text[j] != quote:
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
        else:
            out.append(text[i])
            i += 1
            continue
        out.append(blank(text[i:j]))
        i = j
    return "".join(out)


def c_calls(root: Path, symbols: set[str]) -> set[str]:
    """The members of `symbols` that the C sources call, not merely declare.

    A declaration is an `extern` statement, `extern <type> name(<params>);`.
    Once those are removed, any remaining `name(` is a call: the C sources
    define none of these functions themselves."""
    called = set()
    for path in sorted((root / "bindings" / "python").glob("*.c")):
        text = re.sub(r"\bextern\b[^;{]*;", " ", strip_c(path.read_text()))
        called |= set(re.findall(r"\b(eth_\w+)\s*\(", text)) & symbols
    return called


def exports(root: Path) -> str:
    """The exported operations and size constants, and which of them the C extension calls."""
    lean = lean_exports(root)
    called = c_calls(root, lean)
    consts = {s for s in lean if "_const_" in s}
    ops = lean - consts

    text = (f"Lean exports {len(ops)} operations and {len(consts)} size constants.\n"
            f"The Python extension calls {len(ops & called)} of the operations "
            f"and {len(consts & called)} of the constants.\n")
    for kind, uncalled in (("operations", ops - called), ("constants", consts - called)):
        if uncalled:
            text += f"Exported {kind} it does not call: {', '.join(f'`{s}`' for s in sorted(uncalled))}.\n"
    return text


def c_lines(root: Path) -> str:
    bindings = root / "bindings" / "python"
    files = sorted(list(bindings.glob("*.c")) + list(bindings.glob("*.h")))
    counts = [(p.name, len(p.read_text().splitlines())) for p in files]
    total = sum(n for _, n in counts)
    each = ", ".join(f"`{name}` ({n})" for name, n in counts)
    return f"{total} lines of hand-written C sit between them and Python: {each}.\n"


def pins(root: Path) -> str:
    """The pinned dependencies: the commit each resolved to, and the tag or branch requested."""
    manifest = {p["name"]: p for p in json.loads((root / "lake-manifest.json").read_text())["packages"]}
    toolchain = (root / "lean-toolchain").read_text().strip()

    def pin(name: str) -> str:
        p = manifest[name]
        rev, requested = p["rev"][:7], p.get("inputRev")
        return f"`{requested}`, commit `{rev}`" if requested and not p["rev"].startswith(requested) else f"`{rev}`"

    return (f"The specification requires no package.\n"
            f"The package requires Mathlib, at {pin('mathlib')}, which only the proofs import.\n"
            f"The Lean toolchain is `{toolchain}`.\n")


GENERATORS = {
    "native": native,
    "unfoldable": unfoldable,
    "exports": exports,
    "c-lines": c_lines,
    "pins": pins,
}


def regenerate(root: Path, doc: str) -> tuple[str, list[str]]:
    """The document with every block regenerated, and the problems found."""
    problems, seen = [], set()

    def fill(m: re.Match) -> str:
        name = m.group(2)
        if name not in GENERATORS:
            problems.append(f"unknown generated block: {name}")
            return m.group(0)
        seen.add(name)
        return m.group(1) + GENERATORS[name](root) + m.group(4)

    out = BLOCK.sub(fill, doc)
    for name in sorted(GENERATORS.keys() - seen):
        problems.append(f"missing generated block: {name}")
    return out, problems


def package_version(root: Path) -> str | None:
    """The `version` in the `[project]` table of `pyproject.toml`.
    Read with a pattern rather than `tomllib`, which needs Python 3.11."""
    text = (root / "pyproject.toml").read_text()
    project = re.search(r"^\[project\]\n(.*?)(?=^\[|\Z)", text, re.M | re.S)
    m = project and re.search(r'^version\s*=\s*"([^"]+)"', project.group(1), re.M)
    return m.group(1) if m else None


def check_version(root: Path, doc: str) -> list[str]:
    version = package_version(root)
    m = VERSION_LINE.search(doc)
    if not m:
        return ["no line naming the package version the document describes"]
    if m.group(1) != version:
        return [f"it describes package version {m.group(1)}, but pyproject.toml declares {version}: "
                "review the document for this version, then update that line"]
    return []


def run(root: Path, check: bool) -> list[str]:
    path = root / "SOUNDNESS.md"
    doc = path.read_text()
    new, problems = regenerate(root, doc)
    problems += check_version(root, doc)
    if check:
        if new != doc:
            problems.append("generated blocks are out of date: run python3 scripts/soundness_facts.py")
    elif new != doc:
        path.write_text(new)
        print("SOUNDNESS.md: generated blocks updated")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0].strip())
    parser.add_argument("--check", action="store_true",
                        help="fail if a generated block is out of date, or the version differs")
    args = parser.parse_args()
    problems = run(ROOT, args.check)
    for p in problems:
        print(f"SOUNDNESS.md: {p}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
