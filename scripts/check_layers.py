"""Check the import rules of ARCHITECTURE.md on the header of every Lean module under `EthLib/`."""

import importlib.util
import re
import sys
import tomllib
from collections import Counter, deque
from collections.abc import Iterable, Mapping, Sequence, Set as AbstractSet
from pathlib import Path
from typing import NamedTuple

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
# The first tier of Cryptography: hashes and Merkle trees, which import no other part of it.
FIRST_TIER = ("Hash", "Merkle")
# The two hash-based signatures, whose modules never reach each other through their imports.
SCHEMES = ("Xmss", "Sphincs")
KIND_NAMES = {"specification": "a specification", "property": "a property", "export": "a C export"}
# The models and the refinement modules of ARCHITECTURE.md "Three kinds of content".
KINDS = "coverage/kinds.toml"

HEADER_WORD = re.compile(r"\s*(module|prelude)\b")
IMPORT = re.compile(r"\s*(?:public\s+)?(meta\s+)?import\s+(?:all\s+)?([^\s]+)")
LIBRARY = re.compile(r"^lean_lib\s+«?([A-Za-z0-9_]+)»?\s+where(.*?)(?=^\S|\Z)", re.M | re.S)
ROOTS = re.compile(r"roots\s*:=\s*#\[(.*?)\]", re.S)
LAYER_ROW = re.compile(r"^\|\s*([A-Za-z]+)\s*\|.*\|\s*`EthLib/([A-Za-z]+)/`\s*\|\s*$", re.M)


class Import(NamedTuple):
    """One import line of a module header."""

    module: str
    meta: bool
    line: int


def read_header(text: str) -> tuple[list[Import], str]:
    """The imports of a Lean file, read from its header, and the code after the header."""
    code = strip_lean(text)
    found, index = [], 0
    while True:
        if word := HEADER_WORD.match(code, index):
            index = word.end()
        elif match := IMPORT.match(code, index):
            module = match.group(2).replace("«", "").replace("»", "")
            # `strip_lean` keeps every newline, so the line number is the one in the file.
            line = code.count("\n", 0, match.start(2)) + 1
            found.append(Import(module, bool(match.group(1)), line))
            index = match.end()
        else:
            return found, code[index:]


def header_imports(text: str) -> list[Import]:
    """The imports of a Lean file, read from its header."""
    return read_header(text)[0]


def imports(text: str) -> list[str]:
    """The modules that a Lean file imports, read from its header."""
    return [found.module for found in header_imports(text)]


def meta_problems(
    headers: dict[str, list[Import]], graph: dict[str, list[str]]
) -> list[tuple[str, Import, str]]:
    """
    Each `meta import` that could let an export run specification code while it is elaborated.

    Each problem is the module that writes the import, the import, and the rule it breaks.

    Under the module system, a module runs imported code at elaboration only through `meta import`.
    But an `elab` defined in another module runs while the module that uses it is elaborated.
    So the check walks every module that an export reaches through its imports, of any kind.
    A `meta import` also makes the code of every module that the imported one reaches runnable.
    So no module on that walk meta-imports a module that reaches a specification.

    A specification never uses `meta import`, whether an export reaches it or not.
    An `elab` or a `meta def` written in a specification with no `meta import` is not seen here.
    """
    reaches: dict[str, bool] = {}

    def reaches_specification(module: str) -> bool:
        if module not in reaches:
            # Lean rejects a cycle of imports; the mark only keeps a broken tree from looping.
            reaches[module] = False
            reaches[module] = module in graph and (
                kind(module) == "specification"
                or any(reaches_specification(imported) for imported in graph[module])
            )
        return reaches[module]

    # Walk breadth first, and remember an export that reaches each module.
    exports = [name for name in sorted(graph) if "Exports" in name.split(".")]
    reached = {name: name for name in exports}
    queue = deque(exports)
    while queue:
        current = queue.popleft()
        for imported in graph[current]:
            if imported in graph and imported not in reached:
                reached[imported] = reached[current]
                queue.append(imported)

    problems = []
    for name in sorted(headers):
        for found in headers[name]:
            if not found.meta:
                continue
            if kind(name) == "specification":
                problems.append((name, found, "a specification never uses `meta import`"))
            elif name in reached and reaches_specification(found.module):
                via = "" if reached[name] == name else f"{reached[name]} reaches it, and "
                rule = f"{via}no export runs specification code while it is elaborated"
                problems.append((name, found, rule))
    return problems


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


def first_tier(module: str) -> bool:
    """Whether a module sits in the first tier of Cryptography."""
    parts = module.split(".")
    return parts[:2] == ["EthLib", "Cryptography"] and len(parts) > 2 and parts[2] in FIRST_TIER


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


def external_reached(graph: dict[str, list[str]]) -> dict[str, str]:
    """
    The first module outside EthLib and the toolchain that each property reaches, if any.

    The search passes only through properties.
    A specification or an export on the way reports its own imports.
    So an import that breaks the rule is reported once, where it is written.
    """
    found: dict[str, str | None] = {}

    def visit(name: str) -> str | None:
        if name in found:
            return found[name]
        # Lean rejects a cycle of imports; the mark only keeps a broken tree from looping.
        found[name] = None
        for imported in graph[name]:
            package = imported.split(".")[0]
            if package != "EthLib":
                reached = None if package in TOOLCHAIN else imported
            elif imported in graph and kind(imported) == "property":
                reached = visit(imported)
            else:
                reached = None
            if reached is not None:
                found[name] = reached
                break
        return found[name]

    for name in sorted(graph):
        if kind(name) == "property":
            visit(name)
    return {name: reached for name, reached in found.items() if reached is not None}


def reach_problems(graph: dict[str, list[str]]) -> list[tuple[str, str, str]]:
    """
    Each import of a property through which a C export reaches another library.

    Each problem is the export, the property it imports, and the module outside that it reaches.
    An export that imports an outside module itself breaks another rule, so it is not reported here.
    """
    reached = external_reached(graph)
    problems = []
    for name in sorted(graph):
        if kind(name) != "export":
            continue
        for imported in graph[name]:
            if imported in reached and kind(imported) == "property":
                problems.append((name, imported, reached[imported]))
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
    if (
        source == "specification"
        and first_tier(module)
        and layer(imported) == "Cryptography"
        and target == "specification"
        and not first_tier(imported)
    ):
        problems.append("hashes and Merkle trees import no other part of Cryptography")
    here, there = layer(module), layer(imported)
    if module not in AGGREGATORS and here and there and here != there:
        if LAYERS[there] > LAYERS[here]:
            problems.append(f"{here} sits below {there}")
        elif LAYERS[there] == LAYERS[here]:
            problems.append(f"{here} and {there} never import each other")
    return problems


class Kinds(NamedTuple):
    """The model prefixes and the refinement modules that the kinds file declares."""

    models: tuple[str, ...]
    refinement: tuple[str, ...]


class KindsError(ValueError):
    """The kinds file is not valid TOML, or is not two lists of distinct module names."""


def read_kinds(text: str) -> Kinds:
    """The declarations of a kinds file, or a `KindsError` that says what is wrong."""
    try:
        declared: dict[str, object] = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        raise KindsError(f"not valid TOML: {error}") from error
    if unknown := sorted(set(declared) - set(Kinds._fields)):
        raise KindsError(f"unknown keys {unknown}; the file holds only {list(Kinds._fields)}")

    def names(key: str) -> tuple[str, ...]:
        if key not in declared:
            raise KindsError(f"the key {key} is missing")
        value = declared[key]
        if not isinstance(value, list):
            raise KindsError(f"{key} must be a list of module names, each a string")
        strings = tuple(name for name in value if isinstance(name, str))
        if len(strings) != len(value):
            raise KindsError(f"{key} must be a list of module names, each a string")
        if duplicates := sorted(name for name, count in Counter(strings).items() if count > 1):
            raise KindsError(f"{key} lists {duplicates} more than once")
        return strings

    return Kinds(models=names("models"), refinement=names("refinement"))


def is_model(module: str, models: Iterable[str]) -> bool:
    """Whether a module is a model: a declared prefix, or a module under one."""
    return any(module == prefix or module.startswith(prefix + ".") for prefix in models)


def reaches_model(graph: Mapping[str, Sequence[str]], models: Sequence[str]) -> dict[str, bool]:
    """Whether each module is a model or reaches one through its imports."""
    reached: dict[str, bool] = {}

    def visit(name: str) -> bool:
        if name not in reached:
            # Lean rejects a cycle of imports; the mark only keeps a broken tree from looping.
            reached[name] = False
            reached[name] = is_model(name, models) or any(
                visit(imported) for imported in graph[name] if imported in graph
            )
        return reached[name]

    for name in sorted(graph):
        visit(name)
    return reached


def stale_kinds(
    graph: Mapping[str, Sequence[str]], gatherers: AbstractSet[str], kinds: Kinds
) -> list[str]:
    """
    Each declaration of the kinds file that names no module, or a module of the wrong kind.

    A refinement module is checked only to reach a model: only a reviewer can see its theorems.
    """
    stale = []
    for prefix in kinds.models:
        if not any(is_model(name, [prefix]) for name in graph):
            stale.append(f"{KINDS}: no module is under the model {prefix}")
        elif kind(prefix) != "property":
            stale.append(f"{KINDS}: the model {prefix} is not under a Proofs directory")
    reached = reaches_model(graph, kinds.models)
    for name in kinds.refinement:
        if name not in graph:
            reason = "does not exist"
        elif kind(name) != "property":
            reason = "is not a property module"
        elif is_model(name, kinds.models):
            reason = "is a model"
        elif name in AGGREGATORS:
            reason = "is an aggregator"
        elif name in gatherers:
            reason = "only gathers imports"
        elif not reached[name]:
            reason = "reaches no model"
        else:
            continue
        stale.append(f"{KINDS}: the refinement module {name} {reason}")
    return stale


def model_imports(
    graph: Mapping[str, Sequence[str]], gatherers: AbstractSet[str], kinds: Kinds
) -> list[tuple[str, str]]:
    """
    Each direct import of a model by a property module that the kinds file does not allow.

    Each import is the module that writes it and the model it names.
    A module whose body holds nothing but imports gathers other modules and states nothing.
    So it is exempt, as are the aggregators and the models themselves.
    """
    exempt = gatherers | AGGREGATORS | set(kinds.refinement)
    return [
        (name, imported)
        for name in sorted(graph)
        if kind(name) == "property" and not is_model(name, kinds.models) and name not in exempt
        for imported in graph[name]
        if is_model(imported, kinds.models)
    ]


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
    parsed = {name: read_header(path.read_text(encoding="utf-8")) for name, path in modules.items()}
    headers = {name: lines for name, (lines, _) in parsed.items()}
    graph = {name: [found.module for found in lines] for name, lines in headers.items()}
    gatherers = {name for name, (_, rest) in parsed.items() if not rest.strip()}

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

    kinds_path = root / KINDS
    kinds = None
    if not kinds_path.exists():
        problems.append(f"{KINDS}: missing")
    else:
        try:
            kinds = read_kinds(kinds_path.read_text(encoding="utf-8"))
        except KindsError as error:
            problems.append(f"{KINDS}: {error}")
    if kinds is not None:
        problems += stale_kinds(graph, gatherers, kinds)
        for name, model in model_imports(graph, gatherers, kinds):
            if (name, model) in baseline:
                used.add((name, model))
            else:
                problems.append(
                    f"{modules[name].relative_to(root)}: imports the model {model}, "
                    f"but {KINDS} does not declare it a refinement module"
                )
    for name, imported in sorted(baseline - used):
        # Without the kinds file, an entry between two properties may still be needed.
        if kinds is None and kind(name) == kind(imported) == "property":
            continue
        problems.append(
            f"scripts/check_layers_baseline.txt: {name} {imported} "
            "breaks no rule any more; remove the entry"
        )

    for name, found, rule in meta_problems(headers, graph):
        problems.append(
            f"{modules[name].relative_to(root)}:{found.line}: meta-imports {found.module}, "
            f"but {rule}"
        )

    for name, imported, target in scheme_problems(graph):
        via = "" if imported == target else f", which reaches {target}"
        problems.append(
            f"{modules[name].relative_to(root)}: imports {imported}{via}, "
            f"but {scheme(name)} and {scheme(target)} never import each other"
        )

    for name, imported, target in reach_problems(graph):
        problems.append(
            f"{modules[name].relative_to(root)}: imports {imported}, which reaches {target}, "
            "but a C export reaches nothing beyond EthLib and the toolchain"
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
