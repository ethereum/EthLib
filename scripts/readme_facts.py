"""
Keep each primitive's README in step with the code it describes.

A primitive's README, such as `EthLib/Cryptography/Kzg/README.md`, is mostly
prose reviewed by hand. This script checks what the page cannot keep by itself.

The facts that change with the code are generated between markers, as in
SOUNDNESS.md:

    <!-- generated: NAME -->
    ...
    <!-- end generated -->

`baseline` lists the module's entries in `scripts/check_decls_baseline.txt`.
`vectors` counts the module's pinned test vectors, per handler. A page has a
`vectors` block exactly when `tests/cryptography/<module>/SHA256SUMS` exists.

Every name a page cites in parentheses, such as (`sqrt_ok`, `Compress.lean`),
must be a file the page describes or a declaration in one. In a table whose
header names a `Lean` column, the Lean name must be declared in the row's file,
and a `C export` must be exported.

The prose is checked against the files the page describes: the module's code,
proofs and exports, and every other local file the page cites, by a path in
backticks or a relative link. A cited directory is not followed. Another page's
README is not tracked either, so that two pages can cite each other. The page
records a digest of those files:

    <!-- reviewed: 0123456789abcdef -->

When one of them changes, the check fails until someone reads the page again
and records the new digest. The script records it only when asked to.

Each module in `PAGES` must have a README, so deleting a page fails rather than
dropping its checks. A README in any other module is checked too.

    python3 scripts/readme_facts.py                  # rewrite the generated blocks
    python3 scripts/readme_facts.py --check          # fail on any drift
    python3 scripts/readme_facts.py --reviewed Kzg   # record that the KZG page was checked again

Only the standard library is used, and Python 3.10 is enough, so the check
needs no Lean, no build and no install step.
"""
import argparse
import hashlib
import importlib.util
import re
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

# Share the baseline and Lean parsers of `soundness_facts.py`; `scripts` is not a package.
spec = importlib.util.spec_from_file_location("soundness_facts", HERE / "soundness_facts.py")
soundness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(soundness)

CRYPTO = Path("EthLib") / "Cryptography"
PAGES = ("Bls", "Kzg", "Xmss")
REVIEWED = re.compile(r"<!-- reviewed:\s*([0-9a-f]*)\s*-->")
FENCE = re.compile(r"^```[^\n]*\n(.*?)^```", re.M | re.S)
IDENT = re.compile(r"[A-Za-z_][\w.'!?]*")
LEAN_FILE = re.compile(r"[\w/]+\.lean")
DECL = re.compile(
    r"\b(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+([^\s(){}\[\]:]+)")


def pages(root: Path, required: tuple[str, ...]) -> list[str]:
    """The modules that must have a README, and every other module that has one."""
    found = {d.name for d in (root / CRYPTO).iterdir() if (d / "README.md").is_file()}
    return sorted(found | set(required))


def module_files(root: Path, module: str) -> set[Path]:
    """The module's code, proofs and exports, relative to `root`, without its README.
    Each of the three has a directory and a root file that imports it."""
    files = set()
    for d in (root / CRYPTO / module, root / CRYPTO / "Proofs" / module):
        if d.is_dir():
            files |= {p for p in d.rglob("*") if p.is_file()}
    for f in (root / CRYPTO / f"{module}.lean", root / CRYPTO / "Proofs" / f"{module}.lean",
              root / CRYPTO / "Exports" / f"{module}.lean"):
        if f.is_file():
            files.add(f)
    files.discard(root / CRYPTO / module / "README.md")
    return {p.relative_to(root) for p in files}


def resolve(root: Path, module: str, name: str) -> set[Path]:
    """The files that a cited `X.lean` or `dir/X.lean` names.

    The module's own files come first, so `Compress.lean` on the BLS page means
    the BLS code and proofs of that name. Otherwise the name is a path from the
    repository root, such as `lakefile.lean`, or matches files under `EthLib/`."""
    def match(p: Path) -> bool:
        return p.as_posix() == name or p.as_posix().endswith("/" + name)

    own = {p for p in module_files(root, module) if match(p)}
    if own:
        return own
    if (root / name).is_file():
        return {Path(name)}
    return {p.relative_to(root) for p in (root / "EthLib").rglob("*.lean") if match(p.relative_to(root))}


def prose(doc: str) -> str:
    """The page without its fenced blocks."""
    return FENCE.sub("", doc)


def cited_local(root: Path, module: str, doc: str) -> set[Path]:
    """The local files other than Lean that the page cites, relative to `root`.

    A citation is a backticked path from the repository root, such as
    `tests/cryptography/kzg/SHA256SUMS`, or a relative link. A path that names
    no local file, such as one in another repository, is not one. The generated
    blocks are the script's own text, so they cite nothing."""
    text = soundness.BLOCK.sub(lambda m: m.group(1) + m.group(4), doc)
    page_dir = root / CRYPTO / module
    found = set()
    for tok in re.findall(r"`([^`\s]+)`", text):
        if not tok.endswith(".lean") and (root / tok).is_file():
            found.add((root / tok).resolve())
    for target in re.findall(r"\]\(([^)\s#]+)", text):
        if "://" not in target and (page_dir / target).is_file():
            found.add((page_dir / target).resolve())
    readmes = {(root / CRYPTO / m / "README.md").resolve() for m in pages(root, ())}
    base = root.resolve()
    return {f.relative_to(base) for f in found - readmes if f.is_relative_to(base)}


def citations(doc: str) -> list[str]:
    """The backticked tokens inside parentheses, outside fenced blocks.
    One level of nested parentheses is kept, for a link inside a parenthesis."""
    groups = re.findall(r"\(([^()]*(?:\([^()]*\)[^()]*)*)\)", prose(doc))
    return [tok for g in groups for tok in re.findall(r"`([^`\n]+)`", g)]


def tables(doc: str) -> list[dict[str, str]]:
    """The rows of every fenced table whose header has a `Lean` column, as {column title: cell}.

    A column starts where its title starts in the header, and titles are
    separated by at least two spaces, so `C export` is one title."""
    rows = []
    for block in FENCE.findall(doc):
        lines = block.splitlines()
        if not lines:
            continue
        columns = [(m.start(), m.group()) for m in re.finditer(r"\S+(?: \S+)*", lines[0])]
        if "Lean" not in (title for _, title in columns):
            continue
        for line in lines[1:]:
            row = {}
            for i, (start, title) in enumerate(columns):
                end = columns[i + 1][0] if i + 1 < len(columns) else len(line)
                row[title] = line[start:end].strip()
            # A file may sit in a column without a title.
            if "file" not in row and (m := LEAN_FILE.search(line)):
                row["file"] = m.group()
            rows.append(row)
    return rows


def declarations(root: Path, files: set[Path]) -> set[str]:
    """The last component of every name declared in the Lean files among `files`."""
    names = set()
    for f in files:
        if f.suffix == ".lean":
            text = soundness.strip_lean((root / f).read_text())
            names |= {n.split(".")[-1] for n in DECL.findall(text)}
    return names


def check_names(root: Path, module: str, doc: str) -> tuple[set[Path], list[str]]:
    """The other files the page cites, and each citation that names nothing."""
    problems, cited = [], set()
    files = [tok for tok in re.findall(r"`([^`\n]+)`", doc) if LEAN_FILE.fullmatch(tok)]
    files += [row["file"] for row in tables(doc) if row.get("file")]
    for name in files:
        found = resolve(root, module, name)
        if len(found) == 1 or found and found <= module_files(root, module):
            cited |= found
        elif found:
            problems.append(f"cites `{name}`, which names several files: give its directory")
        else:
            problems.append(f"cites `{name}`, which names no file")

    described = module_files(root, module) | cited
    declared = declarations(root, described)
    for tok in citations(doc):
        if IDENT.fullmatch(tok) and not tok.endswith(".lean") and tok.split(".")[-1] not in declared:
            problems.append(f"cites `{tok}`, which no file it describes declares")

    exported = soundness.lean_exports(root)
    for row in tables(doc):
        lean, file = row["Lean"].split(), row.get("file")
        if lean and file and lean[0].split(".")[-1] not in declarations(root, resolve(root, module, file)):
            problems.append(f"lists `{lean[0]}` in `{file}`, which does not declare it")
        for symbol in row.get("C export", "").split():
            if symbol not in exported:
                problems.append(f"lists the C export `{symbol}`, which no export module declares")
    return cited, problems


def digest(root: Path, files: set[Path]) -> str:
    """A short digest of the paths and contents of `files`."""
    h = hashlib.sha256()
    for f in sorted(files, key=Path.as_posix):
        h.update(f.as_posix().encode() + b"\0" + hashlib.sha256((root / f).read_bytes()).digest())
    return h.hexdigest()[:16]


def baseline(root: Path, module: str) -> str:
    prefix = f"EthLib.Cryptography.{module}."
    found = sorted((soundness.readable(d), k) for k, d in soundness.baseline(root)
                   if d.startswith(prefix) or d.startswith("_private." + prefix))
    if not found:
        return "`scripts/check_decls_baseline.txt` lists no finding in this module.\n"
    return ("`scripts/check_decls_baseline.txt` lists these findings in this module:\n\n"
            + "".join(f"- {d}, `{k}`\n" for d, k in found))


def vectors_path(root: Path, module: str) -> Path:
    return root / "tests" / "cryptography" / module.lower() / "SHA256SUMS"


def vectors(root: Path, module: str) -> str:
    """The pinned cases per handler. Each line of `SHA256SUMS` names a file
    `<handler>/<case>/...`, and a case may have several files."""
    cases = set()
    for line in vectors_path(root, module).read_text().splitlines():
        if line.strip():
            handler, case = line.split(None, 1)[1].split("/")[:2]
            cases.add((handler, case))
    counts = Counter(handler for handler, _ in cases)
    width = max(map(len, counts)) + 5
    table = "".join(f"{h:<{width}}{n:>5}\n" for h, n in sorted(counts.items()))
    return (f"`tests/cryptography/{module.lower()}/` holds {len(cases)} cases:\n\n"
            f"```text\n{'handler':<{width}}cases\n{table}```\n")


def generators(root: Path, module: str) -> dict:
    gens = {"baseline": baseline}
    if vectors_path(root, module).is_file():
        gens["vectors"] = vectors
    return gens


def regenerate(root: Path, module: str, doc: str) -> tuple[str, list[str]]:
    """The page with every block regenerated, and the problems found."""
    gens, problems, seen = generators(root, module), [], set()

    def fill(m: re.Match) -> str:
        name = m.group(2)
        if name not in gens:
            problems.append(f"unknown generated block: {name}")
            return m.group(0)
        seen.add(name)
        return m.group(1) + gens[name](root, module) + m.group(4)

    out = soundness.BLOCK.sub(fill, doc)
    for name in sorted(gens.keys() - seen):
        problems.append(f"missing generated block: {name}")
    return out, problems


def run(root: Path, check: bool, reviewed: tuple[str, ...] = (), required: tuple[str, ...] = PAGES) -> list[str]:
    problems = []
    for name in sorted(set(reviewed) - set(pages(root, required))):
        problems.append(f"--reviewed {name}: no module of that name has a README")
    for module in pages(root, required):
        path = root / CRYPTO / module / "README.md"
        if not path.is_file():
            problems.append(f"{path.relative_to(root)}: missing: every module in PAGES must have a README")
            continue
        doc = path.read_text()
        new, found = regenerate(root, module, doc)
        cited, named = check_names(root, module, doc)
        found += named

        current = digest(root, module_files(root, module) | cited | cited_local(root, module, doc))
        recorded = REVIEWED.search(doc)
        if not recorded:
            found.append("no `<!-- reviewed: ... -->` line")
        elif module in reviewed:
            new = REVIEWED.sub(f"<!-- reviewed: {current} -->", new, count=1)
        elif recorded.group(1) != current:
            found.append("the files it describes changed since it was last reviewed: "
                         f"read it again, then run python3 scripts/readme_facts.py --reviewed {module}")

        if check:
            if new != doc:
                found.append("generated blocks are out of date: run python3 scripts/readme_facts.py")
        elif new != doc:
            path.write_text(new)
            print(f"{path.relative_to(root)}: updated")
        problems += [f"{path.relative_to(root)}: {p}" for p in found]
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0].strip())
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="fail on any drift, and change nothing")
    mode.add_argument("--reviewed", nargs="+", default=(), metavar="MODULE",
                      help="record that these pages were read again against the files they describe")
    args = parser.parse_args()
    problems = run(ROOT, args.check, tuple(args.reviewed))
    for p in problems:
        print(p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
