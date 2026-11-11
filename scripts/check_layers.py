"""Check the import rules of ARCHITECTURE.md on the header of every Lean module under `EthLib/`."""

import importlib.util
import re
import sys
from collections import deque
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
# The aggregators import every layer, so the layer order does not apply to them.
AGGREGATORS = {"EthLib", "EthLib.Proofs", "EthLib.Exports"}
# The packages of the Lean toolchain, which a specification and a C export may import.
TOOLCHAIN = {"Init", "Std", "Lean"}
# The two hash-based signatures, whose modules never reach each other through their imports.
SCHEMES = ("Xmss", "Sphincs")
KIND_NAMES = {"specification": "a specification", "property": "a property", "export": "a C export"}

HEADER_WORD = re.compile(r"\s*(module|prelude)\b")
IMPORT = re.compile(r"\s*(?:public\s+)?(meta\s+)?import\s+(?:all\s+)?([^\s]+)")
LIBRARY = re.compile(r"^lean_lib\s+«?([A-Za-z0-9_]+)»?\s+where(.*?)(?=^\S|\Z)", re.M | re.S)
ROOTS = re.compile(r"roots\s*:=\s*#\[(.*?)\]", re.S)
LAYER_ROW = re.compile(r"^\|\s*([A-Za-z]+)\s*\|.*\|\s*`EthLib/([A-Za-z]+)/`\s*\|\s*$", re.M)


def header_imports(text: str) -> list[tuple[str, bool]]:
    """The modules that a Lean file imports, read from its header, each with whether it is meta."""
    code = strip_lean(text)
    found, index = [], 0
    while True:
        if word := HEADER_WORD.match(code, index):
            index = word.end()
        elif match := IMPORT.match(code, index):
            found.append((match.group(2).replace("«", "").replace("»", ""), bool(match.group(1))))
            index = match.end()
        else:
            return found


def imports(text: str) -> list[str]:
    """The modules that a Lean file imports, read from its header."""
    return [module for module, _ in header_imports(text)]


def meta_problems(module: str, meta_imported: list[str]) -> list[str]:
    """
    Each EthLib module that a module of the `Exports` library imports with `meta import`.

    Under the module system, code that runs while a module is elaborated needs `meta import`.
    So a module of `Exports` that meta-imports no EthLib module runs no EthLib code then.
    """
    if "Exports" not in module.split("."):
        return []
    return [imported for imported in meta_imported if imported.split(".")[0] == "EthLib"]


def module_name(path: Path, root: Path) -> str:
    """The Lean module name of a file under `root`."""
    return ".".join(path.relative_to(root).with_suffix("").parts)


def kind(module: str) -> str:
    """The kind of a module: a property, an export or a specification."""
    parts = module.split(".")
    if "Proofs" in parts:
        return "property"
    if "Exports" in parts:
        return "export"
    return "specification"


def layer(module: str) -> str | None:
    """The layer of an `EthLib` module, or None outside the layers."""
    parts = module.split(".")
    return parts[1] if len(parts) > 1 and parts[0] == "EthLib" and parts[1] in LAYERS else None


def scheme(module: str) -> str | None:
    """The hash-based signature whose tree holds a module, if exactly one does."""
    found = [name for name in SCHEMES if name in module.split(".")]
    return found[0] if len(found) == 1 else None


def scheme_problems(graph: dict[str, list[str]]) -> list[tuple[str, str, str]]:
    """Each module of one scheme that reaches the other: the module, its import, the target."""
    problems = []
    for name in sorted(graph):
        own = scheme(name)
        if own is None:
            continue
        # Search breadth first, and remember the import of `name` that each module comes from.
        first = {imported: imported for imported in graph[name] if imported in graph}
        queue = deque(first)
        while queue:
            current = queue.popleft()
            other = scheme(current)
            if other is not None and other != own:
                problems.append((name, first[current], current))
                break
            for imported in graph[current]:
                if imported in graph and imported not in first:
                    first[imported] = first[current]
                    queue.append(imported)
    return problems


def library_roots(lakefile: str) -> list[str]:
    """The root modules of each `lean_lib` of the lakefile; without `roots`, the library itself."""
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
    """The (module, import) pairs that the baseline file allows."""
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
    headers = {
        name: header_imports(path.read_text(encoding="utf-8")) for name, path in modules.items()
    }
    graph = {name: [imported for imported, _ in found] for name, found in headers.items()}

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
                    problems.append(
                        f"{modules[name].relative_to(root)}: imports {imported}, but {problem}"
                    )
    for name, imported in sorted(baseline - used):
        problems.append(
            f"scripts/check_layers_baseline.txt: {name} {imported} "
            "breaks no rule any more; remove the entry"
        )

    for name, found in headers.items():
        for imported in meta_problems(name, [m for m, meta in found if meta]):
            problems.append(
                f"{modules[name].relative_to(root)}: meta-imports {imported}, "
                "but a module of the Exports library runs no EthLib code while it is elaborated"
            )

    for name, imported, target in scheme_problems(graph):
        via = "" if imported == target else f", which reaches {target}"
        problems.append(
            f"{modules[name].relative_to(root)}: imports {imported}{via}, "
            f"but {scheme(name)} and {scheme(target)} never import each other"
        )

    roots = [
        r
        for r in library_roots((root / "lakefile.lean").read_text(encoding="utf-8"))
        if r in modules
    ]
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
            problems.append(
                f"ARCHITECTURE.md lists the layers {sorted(listed)}, "
                f"but this check knows {sorted(LAYERS)}"
            )
    return problems


def main() -> int:
    """Print each problem that the check finds, and return the exit code."""
    problems = check(ROOT)
    for problem in problems:
        print(problem, file=sys.stderr)
    if not problems:
        print("The imports follow the rules of ARCHITECTURE.md.")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
