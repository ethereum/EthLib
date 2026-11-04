"""
Check the import rules of ARCHITECTURE.md on the header of every Lean module under `EthLib/`.

The check fails on each of these, with the module and the import:

- an import into a higher layer, by the order Base, Cryptography, Serialization, Networking,
  then Execution and Consensus side by side, then Engine;
- an import between Execution and Consensus, which only Engine imports together;
- an import of a property (a module with a `Proofs` component) or of a C export (a module with
  an `Exports` component) from a specification;
- an import of anything outside `EthLib` and the Lean toolchain (`Init`, `Std` and `Lean`) from
  a specification or a C export;
- a module that no library root of `lakefile.lean` reaches through its imports;
- a file under `EthLib/` outside a layer, other than the aggregators `EthLib.lean`,
  `EthLib/Proofs.lean` and `EthLib/Exports.lean`.

The order of the layers also keeps Serialization out of every cryptographic module.
The aggregators import every layer, so the layer order does not apply to them.
It also fails when the layer table of ARCHITECTURE.md names other layers than this check.

A pull request that must break an import rule lists the import in
`scripts/check_layers_baseline.txt`, and says why in its description.
An entry that no longer matches an import fails the check too.

    uv run --no-project --python 3.12 python scripts/check_layers.py

Only the standard library is used, so the check needs no Lean and no build.
"""
import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Load the comment stripper of `soundness_facts.py` by path: `scripts` is not a package.
_spec = importlib.util.spec_from_file_location(
    "soundness_facts", Path(__file__).resolve().parent / "soundness_facts.py")
_facts = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_facts)
strip_lean = _facts.strip_lean

# The layers of ARCHITECTURE.md "Layers", by rank. Execution and Consensus share a rank.
LAYERS = {
    "Base": 0,
    "Cryptography": 1,
    "Serialization": 2,
    "Networking": 3,
    "Execution": 4,
    "Consensus": 4,
    "Engine": 5,
}
AGGREGATORS = {"EthLib", "EthLib.Proofs", "EthLib.Exports"}
TOOLCHAIN = {"Init", "Std", "Lean"}
KIND_NAMES = {"specification": "a specification", "property": "a property",
              "export": "a C export"}

HEADER_WORD = re.compile(r"\s*(module|prelude)\b")
IMPORT = re.compile(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s]+)")
LIBRARY = re.compile(r"^lean_lib\s+«?([A-Za-z0-9_]+)»?\s+where(.*?)(?=^\S|\Z)", re.M | re.S)
ROOTS = re.compile(r"roots\s*:=\s*#\[(.*?)\]", re.S)
LAYER_ROW = re.compile(r"^\|\s*([A-Za-z]+)\s*\|.*\|\s*`EthLib/([A-Za-z]+)/`\s*\|\s*$", re.M)


def imports(text: str) -> list[str]:
    """The modules that a Lean file imports, read from its header."""
    code = strip_lean(text)
    found, index = [], 0
    while True:
        if word := HEADER_WORD.match(code, index):
            index = word.end()
        elif match := IMPORT.match(code, index):
            found.append(match.group(1).replace("«", "").replace("»", ""))
            index = match.end()
        else:
            return found


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def kind(module: str) -> str:
    parts = module.split(".")
    if "Proofs" in parts:
        return "property"
    if "Exports" in parts:
        return "export"
    return "specification"


def layer(module: str) -> str | None:
    parts = module.split(".")
    return parts[1] if len(parts) > 1 and parts[0] == "EthLib" and parts[1] in LAYERS else None


def library_roots(lakefile: str) -> list[str]:
    """The root modules of each `lean_lib` of the lakefile.

    A library without `roots` has one root, named after the library."""
    roots = []
    for name, body in LIBRARY.findall(lakefile):
        if listed := ROOTS.search(body):
            roots += re.findall(r"`([A-Za-z0-9_.]+)", listed.group(1))
        else:
            roots.append(name)
    return roots


def import_problems(module: str, imported: str) -> list[str]:
    """Why one import breaks a rule, if it does."""
    problems = []
    source, target = kind(module), kind(imported)
    package = imported.split(".")[0]
    if package != "EthLib":
        if source != "property" and package not in TOOLCHAIN:
            problems.append(f"{KIND_NAMES[source]} imports only EthLib and the toolchain")
        return problems
    if source == "specification" and target != "specification":
        problems.append(f"a specification never imports {KIND_NAMES[target]}")
    here, there = layer(module), layer(imported)
    if module not in AGGREGATORS and here and there and here != there:
        if LAYERS[there] > LAYERS[here]:
            problems.append(f"{here} sits below {there}")
        elif LAYERS[there] == LAYERS[here]:
            problems.append(f"{here} and {there} never import each other")
    return problems


def read_baseline(path: Path) -> set[tuple[str, str]]:
    entries = set()
    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            fields = line.split("#", 1)[0].split()
            if len(fields) == 2:
                entries.add((fields[0], fields[1]))
    return entries


def check(root: Path) -> list[str]:
    """Every problem in the repository at `root`, one line each."""
    problems = []
    files = sorted((root / "EthLib").rglob("*.lean")) + sorted(root.glob("EthLib.lean"))
    modules = {module_name(path, root): path for path in files}
    graph = {name: imports(path.read_text(encoding="utf-8")) for name, path in modules.items()}

    for name, path in modules.items():
        if name not in AGGREGATORS and layer(name) is None:
            problems.append(f"{path.relative_to(root)}: not in a layer of ARCHITECTURE.md")

    baseline = read_baseline(root / "scripts" / "check_layers_baseline.txt")
    used = set()
    for name, imported_list in graph.items():
        for imported in imported_list:
            found = import_problems(name, imported)
            if found and (name, imported) in baseline:
                used.add((name, imported))
            elif found:
                for problem in found:
                    problems.append(f"{modules[name].relative_to(root)}: "
                                    f"imports {imported}, but {problem}")
    for name, imported in sorted(baseline - used):
        problems.append(f"scripts/check_layers_baseline.txt: {name} {imported} "
                        "breaks no rule any more; remove the entry")

    roots = [r for r in library_roots((root / "lakefile.lean").read_text(encoding="utf-8"))
             if r in modules]
    if not roots:
        problems.append("lakefile.lean: no library root under EthLib/ found")
    reached, stack = set(roots), list(roots)
    while stack:
        for imported in graph[stack.pop()]:
            if imported in modules and imported not in reached:
                reached.add(imported)
                stack.append(imported)
    for name in sorted(set(modules) - reached):
        problems.append(f"{modules[name].relative_to(root)}: no library root imports it")

    architecture = root / "ARCHITECTURE.md"
    if architecture.exists():
        listed = {directory for _, directory in LAYER_ROW.findall(architecture.read_text())}
        if listed != set(LAYERS):
            problems.append(f"ARCHITECTURE.md lists the layers {sorted(listed)}, "
                            f"but this check knows {sorted(LAYERS)}")
    return problems


def main() -> int:
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    if not problems:
        print("The imports follow the rules of ARCHITECTURE.md.")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
