"""Tests of `check_layers.py` on small repositories in a temporary directory."""

import importlib.util
import tempfile
import unittest
from collections.abc import Mapping
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_layers", HERE / "check_layers.py")
assert spec and spec.loader
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
| Engine | g | `EthLib/Engine/` |
| Consensus | c | `EthLib/Consensus/` |
| Execution | e | `EthLib/Execution/` |
| Networking | n | `EthLib/Networking/` |
| Serialization | s | `EthLib/Serialization/` |
| Cryptography | c | `EthLib/Cryptography/` |
| Base | b | `EthLib/Base/` |
"""

# A tree that follows every rule: each module of a layer, with its imports.
GOOD = {
    "EthLib": [
        "EthLib.Base.A",
        "EthLib.Cryptography.A",
        "EthLib.Serialization.A",
        "EthLib.Networking.A",
        "EthLib.Execution.A",
        "EthLib.Consensus.A",
        "EthLib.Engine.A",
    ],
    "EthLib.Proofs": ["EthLib.Execution.Proofs.A"],
    "EthLib.Exports": ["EthLib.Execution.Exports.A"],
    "EthLib.Base.A": ["Init.Data.List"],
    "EthLib.Cryptography.A": ["EthLib.Base.A", "Std.Data.HashMap"],
    "EthLib.Serialization.A": ["EthLib.Cryptography.A", "Lean.Data.Json"],
    "EthLib.Networking.A": ["EthLib.Serialization.A"],
    "EthLib.Execution.A": ["EthLib.Networking.A", "EthLib.Base.A"],
    "EthLib.Consensus.A": ["EthLib.Networking.A"],
    "EthLib.Engine.A": ["EthLib.Execution.A", "EthLib.Consensus.A"],
    "EthLib.Execution.Proofs.A": ["EthLib.Execution.A", "Mathlib.Tactic"],
    "EthLib.Execution.Exports.A": ["EthLib.Execution.A"],
}


def header(imported: list[str]) -> str:
    return "module\n\n" + "".join(f"public import {name}\n" for name in imported) + "\ndef x := 1\n"


class Tree:
    """A temporary repository with the given modules and imports."""

    def __init__(
        self,
        modules: Mapping[str, list[str] | str],
        lakefile: str = LAKEFILE,
        baseline: str = "",
        architecture: str = ARCHITECTURE,
    ):
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


def with_imports(module: str, *imported: str) -> dict[str, list[str]]:
    tree = {k: list(v) for k, v in GOOD.items()}
    tree[module] = tree[module] + list(imported)
    return tree


def with_modules(*added: dict[str, list[str]]) -> dict[str, list[str] | str]:
    """The good tree with more modules, each imported by the root `EthLib`."""
    tree: dict[str, list[str] | str] = {k: list(v) for k, v in GOOD.items()}
    root = list(GOOD["EthLib"])
    for module in added:
        tree |= module
        root += list(module)
    tree["EthLib"] = root
    return tree


class Rules(unittest.TestCase):
    def assert_fails(self, tree: dict, text: str) -> None:
        problems = Tree(tree).problems()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn(text, problems[0])

    def test_good_tree(self):
        self.assertEqual(Tree(GOOD).problems(), [])

    def test_repository(self):
        self.assertEqual(layers.check(HERE.parent), [])

    def test_higher_layer(self):
        self.assert_fails(
            with_imports("EthLib.Base.A", "EthLib.Cryptography.A"), "Base sits below Cryptography"
        )

    def test_cryptography_never_imports_serialization(self):
        self.assert_fails(
            with_imports("EthLib.Cryptography.A", "EthLib.Serialization.A"),
            "Cryptography sits below Serialization",
        )

    def test_hash_imports_a_signature(self):
        tree = with_modules(
            {"EthLib.Cryptography.Hash.A": ["EthLib.Cryptography.Bls.A"]},
            {"EthLib.Cryptography.Bls.A": []},
        )
        self.assert_fails(
            tree,
            "EthLib/Cryptography/Hash/A.lean: imports EthLib.Cryptography.Bls.A, "
            "but hashes and Merkle trees import no other part of Cryptography",
        )

    def test_merkle_tree_imports_a_module_beside_the_tiers(self):
        tree = with_modules(
            {"EthLib.Cryptography.Merkle": ["EthLib.Cryptography.Montgomery"]},
            {"EthLib.Cryptography.Montgomery": []},
        )
        self.assert_fails(tree, "hashes and Merkle trees import no other part of Cryptography")

    def test_first_tier_imports_itself_and_base(self):
        tree = with_modules(
            {"EthLib.Cryptography.Hash.A": ["EthLib.Cryptography.Hash.B", "EthLib.Base.A"]},
            {"EthLib.Cryptography.Hash.B": ["EthLib.Cryptography.Merkle.Tree"]},
            {"EthLib.Cryptography.Merkle.Tree": []},
            {"EthLib.Cryptography.Bls.A": ["EthLib.Cryptography.Hash.A"]},
        )
        self.assertEqual(Tree(tree).problems(), [])

    def test_property_of_a_hash_imports_other_cryptography(self):
        tree = with_imports("EthLib.Proofs", "EthLib.Cryptography.Hash.Proofs.A")
        tree |= {
            "EthLib.Cryptography.Hash.Proofs.A": ["EthLib.Cryptography.A"],
        }
        self.assertEqual(Tree(tree).problems(), [])

    def test_hash_imports_a_property_once(self):
        # The import breaks the rule for properties, so it is reported once, for that rule.
        tree = with_modules({"EthLib.Cryptography.Hash.A": ["EthLib.Cryptography.Proofs.A"]})
        tree |= with_imports("EthLib.Proofs", "EthLib.Cryptography.Proofs.A")
        tree["EthLib"] = [*GOOD["EthLib"], "EthLib.Cryptography.Hash.A"]
        tree["EthLib.Cryptography.Proofs.A"] = []
        self.assert_fails(tree, "a specification never imports a property")

    def test_higher_layer_from_a_property(self):
        tree = with_imports("EthLib.Execution.Proofs.A", "EthLib.Consensus.A")
        self.assert_fails(tree, "Execution and Consensus never import each other")

    def test_execution_and_consensus(self):
        self.assert_fails(
            with_imports("EthLib.Consensus.A", "EthLib.Execution.A"),
            "Consensus and Execution never import each other",
        )

    def test_engine_sits_above_execution_and_consensus(self):
        self.assert_fails(
            with_imports("EthLib.Execution.A", "EthLib.Engine.A"), "Execution sits below Engine"
        )
        self.assert_fails(
            with_imports("EthLib.Consensus.A", "EthLib.Engine.A"), "Consensus sits below Engine"
        )

    def test_specification_imports_a_property(self):
        self.assert_fails(
            with_imports("EthLib.Execution.A", "EthLib.Base.Proofs.A")
            | {"EthLib.Base.Proofs.A": []},
            "a specification never imports a property",
        )

    def test_specification_imports_an_export(self):
        self.assert_fails(
            with_imports("EthLib", "EthLib.Execution.Exports.A"),
            "a specification never imports a C export",
        )

    def test_outside_the_toolchain(self):
        self.assert_fails(
            with_imports("EthLib.Base.A", "Batteries.Data.List"),
            "a specification imports only EthLib",
        )
        self.assert_fails(
            with_imports("EthLib.Execution.Exports.A", "Mathlib.Tactic"),
            "a C export imports only EthLib",
        )

    def test_export_reaches_outside_through_a_property(self):
        self.assert_fails(
            with_imports("EthLib.Execution.Exports.A", "EthLib.Execution.Proofs.A"),
            "EthLib/Execution/Exports/A.lean: imports EthLib.Execution.Proofs.A, "
            "which reaches Mathlib.Tactic, "
            "but a C export reaches nothing beyond EthLib and the toolchain",
        )

    def test_export_reaches_outside_through_two_properties(self):
        tree = with_imports("EthLib.Proofs", "EthLib.Execution.Proofs.B")
        tree["EthLib.Execution.Proofs.B"] = ["EthLib.Execution.Proofs.A"]
        tree["EthLib.Execution.Exports.A"] = ["EthLib.Execution.A", "EthLib.Execution.Proofs.B"]
        self.assert_fails(tree, "imports EthLib.Execution.Proofs.B, which reaches Mathlib.Tactic")

    def test_export_reaches_outside_through_another_export(self):
        tree = with_imports("EthLib.Exports", "EthLib.Execution.Exports.B")
        tree["EthLib.Execution.Exports.B"] = ["EthLib.Execution.Exports.A"]
        tree["EthLib.Execution.Exports.A"] = ["EthLib.Execution.A", "EthLib.Execution.Proofs.A"]
        self.assert_fails(
            tree, "EthLib/Execution/Exports/A.lean: imports EthLib.Execution.Proofs.A"
        )

    def test_export_reaches_outside_once_through_a_chain_of_exports(self):
        # Only the property that the second export imports is reported, where the import is written.
        tree = with_imports("EthLib.Exports", "EthLib.Execution.Exports.B")
        tree["EthLib.Execution.Proofs.B"] = ["EthLib.Execution.Exports.A"]
        tree["EthLib.Execution.Exports.B"] = ["EthLib.Execution.A", "EthLib.Execution.Proofs.B"]
        tree["EthLib.Execution.Exports.A"] = ["EthLib.Execution.A", "EthLib.Execution.Proofs.A"]
        self.assert_fails(
            tree, "EthLib/Execution/Exports/A.lean: imports EthLib.Execution.Proofs.A"
        )

    def test_export_imports_a_property_inside_ethlib(self):
        tree = with_imports("EthLib.Exports", "EthLib.Execution.Exports.Proofs.A")
        tree["EthLib.Execution.Exports.Proofs.A"] = ["EthLib.Execution.Exports.A"]
        self.assertEqual(Tree(tree).problems(), [])

    def test_orphan(self):
        self.assert_fails(GOOD | {"EthLib.Base.B": []}, "EthLib/Base/B.lean: no library root")

    def test_outside_a_layer(self):
        tree = with_imports("EthLib", "EthLib.Chain.A") | {"EthLib.Chain.A": []}
        self.assert_fails(tree, "EthLib/Chain/A.lean: not in a layer")

    def test_xmss_imports_sphincs(self):
        tree = with_modules(
            {"EthLib.Cryptography.Xmss.A": ["EthLib.Cryptography.Sphincs.A"]},
            {"EthLib.Cryptography.Sphincs.A": []},
        )
        self.assert_fails(
            tree,
            "imports EthLib.Cryptography.Sphincs.A, but Xmss and Sphincs never import each other",
        )

    def test_sphincs_reaches_xmss_through_a_neutral_module(self):
        tree = with_modules(
            {"EthLib.Cryptography.Sphincs.A": ["EthLib.Cryptography.HashSig"]},
            {"EthLib.Cryptography.HashSig": ["EthLib.Cryptography.Xmss.A"]},
            {"EthLib.Cryptography.Xmss.A": []},
        )
        self.assert_fails(
            tree,
            "EthLib/Cryptography/Sphincs/A.lean: imports EthLib.Cryptography.HashSig, "
            "which reaches EthLib.Cryptography.Xmss.A, "
            "but Sphincs and Xmss never import each other",
        )

    def test_neutral_module_imports_both(self):
        tree = with_modules(
            {
                "EthLib.Cryptography.HashSig": [
                    "EthLib.Cryptography.Xmss.A",
                    "EthLib.Cryptography.Sphincs.A",
                ]
            },
            {"EthLib.Cryptography.Xmss.A": []},
            {"EthLib.Cryptography.Sphincs.A": []},
        )
        self.assertEqual(Tree(tree).problems(), [])

    def test_aggregators_import_every_layer(self):
        tree = with_imports("EthLib.Proofs", "EthLib.Consensus.A", "EthLib.Base.A")
        self.assertEqual(Tree(tree).problems(), [])


class Header(unittest.TestCase):
    def test_import_forms(self):
        text = (
            "/- import EthLib.Commented -/\nmodule\n\n-- import EthLib.Line\n"
            "public import EthLib.A\nimport all EthLib.B\n/- between -/\nmeta import EthLib.C\n"
            "public meta import «EthLib».D\nimport EthLib.E\n\n/-! import EthLib.Doc -/\n"
        )
        self.assertEqual(
            layers.imports(text), ["EthLib.A", "EthLib.B", "EthLib.C", "EthLib.D", "EthLib.E"]
        )

    def test_header_ends_at_the_first_command(self):
        self.assertEqual(layers.imports("module\nimport A\ndef x := 1\nimport B\n"), ["A"])

    def test_library_roots(self):
        self.assertEqual(
            layers.library_roots(LAKEFILE), ["EthLib", "EthLib.Proofs", "EthLib.Exports"]
        )


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
