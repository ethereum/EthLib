"""
Check `check_layers.py` itself, on small repositories built in a temporary directory.

    uv run --no-project --python 3.12 python -m unittest scripts/test_check_layers.py

Only the standard library is used, like the script.
"""
import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_layers", HERE / "check_layers.py")
layers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(layers)

LAKEFILE = """\
package «EthLib» where

@[default_target]
lean_lib «EthLib» where
  requiresModuleSystem := true

lean_lib «Proofs» where
  roots := #[`EthLib.Proofs]

lean_lib «Exports» where
  roots := #[`EthLib.Exports]
"""

ARCHITECTURE = """\
## Layers

| Layer | Holds | Directory |
| --- | --- | --- |
| Consensus | c | `EthLib/Consensus/` |
| Execution | e | `EthLib/Execution/` |
| Networking | n | `EthLib/Networking/` |
| Serialization | s | `EthLib/Serialization/` |
| Cryptography | c | `EthLib/Cryptography/` |
| Base | b | `EthLib/Base/` |
"""

# A tree that follows every rule: each module of a layer, with its imports.
GOOD = {
    "EthLib": ["EthLib.Base.A", "EthLib.Cryptography.A", "EthLib.Serialization.A",
               "EthLib.Networking.A", "EthLib.Execution.A", "EthLib.Consensus.A"],
    "EthLib.Proofs": ["EthLib.Execution.Proofs.A"],
    "EthLib.Exports": ["EthLib.Execution.Exports.A"],
    "EthLib.Base.A": ["Init.Data.List"],
    "EthLib.Cryptography.A": ["EthLib.Base.A", "Std.Data.HashMap"],
    "EthLib.Serialization.A": ["EthLib.Cryptography.A", "Lean.Data.Json"],
    "EthLib.Networking.A": ["EthLib.Serialization.A"],
    "EthLib.Execution.A": ["EthLib.Networking.A", "EthLib.Base.A"],
    "EthLib.Consensus.A": ["EthLib.Networking.A"],
    "EthLib.Execution.Proofs.A": ["EthLib.Execution.A", "Mathlib.Tactic"],
    "EthLib.Execution.Exports.A": ["EthLib.Execution.A"],
}


def header(imported: list[str]) -> str:
    return "module\n\n" + "".join(f"public import {name}\n" for name in imported) + "\ndef x := 1\n"


class Tree:
    """A temporary repository with the given modules and imports."""

    def __init__(self, modules: dict[str, list[str] | str], lakefile: str = LAKEFILE,
                 baseline: str = "", architecture: str = ARCHITECTURE):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "lakefile.lean").write_text(lakefile)
        (self.root / "ARCHITECTURE.md").write_text(architecture)
        (self.root / "scripts").mkdir()
        (self.root / "scripts" / "check_layers_baseline.txt").write_text(baseline)
        for name, body in modules.items():
            path = self.root.joinpath(*name.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(body if isinstance(body, str) else header(body))

    def problems(self) -> list[str]:
        try:
            return layers.check(self.root)
        finally:
            self.tmp.cleanup()


def with_imports(module: str, *imported: str) -> dict[str, list[str] | str]:
    tree: dict[str, list[str] | str] = {k: list(v) for k, v in GOOD.items()}
    tree[module] = tree[module] + list(imported)
    return tree


class Rules(unittest.TestCase):
    def assertFails(self, tree: dict, text: str) -> None:
        problems = Tree(tree).problems()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn(text, problems[0])

    def test_good_tree(self):
        self.assertEqual(Tree(GOOD).problems(), [])

    def test_repository(self):
        self.assertEqual(layers.check(HERE.parent), [])

    def test_higher_layer(self):
        self.assertFails(with_imports("EthLib.Base.A", "EthLib.Cryptography.A"),
                         "Base sits below Cryptography")

    def test_cryptography_never_imports_serialization(self):
        self.assertFails(with_imports("EthLib.Cryptography.A", "EthLib.Serialization.A"),
                         "Cryptography sits below Serialization")

    def test_higher_layer_from_a_property(self):
        tree = with_imports("EthLib.Execution.Proofs.A", "EthLib.Consensus.A")
        self.assertFails(tree, "Execution and Consensus never import each other")

    def test_execution_and_consensus(self):
        self.assertFails(with_imports("EthLib.Consensus.A", "EthLib.Execution.A"),
                         "Consensus and Execution never import each other")

    def test_specification_imports_a_property(self):
        self.assertFails(with_imports("EthLib.Execution.A", "EthLib.Base.Proofs.A")
                         | {"EthLib.Base.Proofs.A": []},
                         "a specification never imports a property")

    def test_specification_imports_an_export(self):
        self.assertFails(with_imports("EthLib", "EthLib.Execution.Exports.A"),
                         "a specification never imports a C export")

    def test_outside_the_toolchain(self):
        self.assertFails(with_imports("EthLib.Base.A", "Batteries.Data.List"),
                         "a specification imports only EthLib")
        self.assertFails(with_imports("EthLib.Execution.Exports.A", "Mathlib.Tactic"),
                         "a C export imports only EthLib")

    def test_orphan(self):
        self.assertFails(GOOD | {"EthLib.Base.B": []}, "EthLib/Base/B.lean: no library root")

    def test_outside_a_layer(self):
        tree = with_imports("EthLib", "EthLib.Chain.A") | {"EthLib.Chain.A": []}
        self.assertFails(tree, "EthLib/Chain/A.lean: not in a layer")

    def test_aggregators_import_every_layer(self):
        tree = with_imports("EthLib.Proofs", "EthLib.Consensus.A", "EthLib.Base.A")
        self.assertEqual(Tree(tree).problems(), [])


class Header(unittest.TestCase):
    def test_import_forms(self):
        text = ("/- import EthLib.Commented -/\nmodule\n\n-- import EthLib.Line\n"
                "public import EthLib.A\nimport all EthLib.B\n/- between -/\nmeta import EthLib.C\n"
                "public meta import «EthLib».D\nimport EthLib.E\n\n/-! import EthLib.Doc -/\n")
        self.assertEqual(layers.imports(text), ["EthLib.A", "EthLib.B", "EthLib.C", "EthLib.D",
                                                "EthLib.E"])

    def test_header_ends_at_the_first_command(self):
        self.assertEqual(layers.imports("module\nimport A\ndef x := 1\nimport B\n"), ["A"])

    def test_library_roots(self):
        self.assertEqual(layers.library_roots(LAKEFILE),
                         ["EthLib", "EthLib.Proofs", "EthLib.Exports"])


class Baseline(unittest.TestCase):
    def test_listed_import_passes(self):
        tree = with_imports("EthLib.Base.A", "EthLib.Cryptography.A")
        baseline = "# Why.\nEthLib.Base.A EthLib.Cryptography.A\n"
        self.assertEqual(Tree(tree, baseline=baseline).problems(), [])

    def test_stale_entry_fails(self):
        problems = Tree(GOOD, baseline="EthLib.Base.A EthLib.Cryptography.A\n").problems()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("breaks no rule any more", problems[0])


class Configuration(unittest.TestCase):
    def test_no_roots(self):
        problems = Tree(GOOD, lakefile="package «EthLib» where\n").problems()
        self.assertIn("lakefile.lean: no library root under EthLib/ found", problems)

    def test_architecture_names_another_layer(self):
        architecture = ARCHITECTURE + "| Chain | c | `EthLib/Chain/` |\n"
        problems = Tree(GOOD, architecture=architecture).problems()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("ARCHITECTURE.md lists the layers", problems[0])


if __name__ == "__main__":
    unittest.main()
