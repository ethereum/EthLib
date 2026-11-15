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
        kinds: str | None = "models = []\nrefinement = []\n",
    ):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "lakefile.lean").write_text(lakefile)
        (self.root / "ARCHITECTURE.md").write_text(architecture)
        (self.root / "scripts").mkdir()
        (self.root / "scripts" / "check_layers_baseline.txt").write_text(baseline)
        if kinds is not None:
            (self.root / "coverage").mkdir()
            (self.root / "coverage" / "kinds.toml").write_text(kinds)
        for name, body in modules.items():
            parts = layers.module_parts(name)
            path = self.root.joinpath(*parts[:-1], parts[-1] + ".lean")
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


def with_proofs(*added: dict[str, list[str] | str]) -> dict[str, list[str] | str]:
    """The good tree with more property modules, each imported by the root `EthLib.Proofs`."""
    tree: dict[str, list[str] | str] = {k: list(v) for k, v in GOOD.items()}
    root = list(GOOD["EthLib.Proofs"])
    for module in added:
        tree |= module
        root += list(module)
    tree["EthLib.Proofs"] = root
    return tree


MODEL = "EthLib.Execution.Proofs.Models.M"
# A model, a property that imports it, and a property that imports that property.
MODEL_TREE: dict[str, list[str] | str] = {
    MODEL: ["EthLib.Execution.A"],
    "EthLib.Execution.Proofs.R": [MODEL],
    "EthLib.Execution.Proofs.S": ["EthLib.Execution.Proofs.R"],
}
MODELLED = with_proofs(MODEL_TREE)
# A property module whose body holds only an import of the model.
GATHERER: dict[str, list[str] | str] = {
    "EthLib.Execution.Proofs.All": f"module\n\npublic import {MODEL}\n"
}


def kinds(models: list[str], refinement: list[str]) -> str:
    """A kinds file that declares the given models and refinement modules."""

    def quoted(names: list[str]) -> str:
        return "[" + ", ".join(f'"{name}"' for name in names) + "]"

    return f"models = {quoted(models)}\nrefinement = {quoted(refinement)}\n"


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

    def test_export_meta_imports_the_specification(self):
        tree: dict[str, list[str] | str] = dict(with_imports("EthLib.Exports"))
        tree["EthLib.Execution.Exports.A"] = (
            "module\n\npublic import EthLib.Execution.A\npublic meta import EthLib.Execution.A\n"
        )
        self.assert_fails(
            tree,
            "EthLib/Execution/Exports/A.lean:4: meta-imports EthLib.Execution.A, "
            "but no export runs specification code while it is elaborated",
        )

    def test_export_proof_meta_imports_the_specification(self):
        tree: dict[str, list[str] | str] = dict(
            with_imports("EthLib.Exports", "EthLib.Execution.Exports.Proofs.A")
        )
        tree["EthLib.Execution.Exports.Proofs.A"] = "module\n\nmeta import EthLib.Execution.A\n"
        self.assert_fails(tree, "meta-imports EthLib.Execution.A")

    def test_imported_property_meta_imports_the_specification(self):
        # The property can define an `elab` that runs specification code inside the export.
        tree: dict[str, list[str] | str] = dict(
            with_imports("EthLib.Execution.Exports.A", "EthLib.Execution.Proofs.A")
        )
        tree["EthLib.Execution.Proofs.A"] = (
            "module\n\npublic import EthLib.Execution.A\npublic meta import EthLib.Execution.A\n"
        )
        self.assert_fails(
            tree,
            "EthLib/Execution/Proofs/A.lean:4: meta-imports EthLib.Execution.A, "
            "but EthLib.Execution.Exports.A reaches it, "
            "and no export runs specification code while it is elaborated",
        )

    def test_specification_meta_imports_the_specification(self):
        # An export imports `EthLib.Execution.A` plainly, so only the meta import breaks a rule.
        tree: dict[str, list[str] | str] = dict(GOOD)
        tree["EthLib.Execution.A"] = (
            "module\n\npublic import EthLib.Networking.A\npublic import EthLib.Base.A\n"
            "public meta import EthLib.Base.A\n"
        )
        self.assert_fails(
            tree,
            "EthLib/Execution/A.lean:5: meta-imports EthLib.Base.A, "
            "but a specification never uses `meta import`",
        )

    def test_specification_that_no_export_reaches_meta_imports(self):
        tree = with_modules({"EthLib.Networking.B": []})
        tree["EthLib.Networking.B"] = "module\n\nmeta import Lean.Elab.Command\n"
        self.assert_fails(
            tree,
            "EthLib/Networking/B.lean:3: meta-imports Lean.Elab.Command, "
            "but a specification never uses `meta import`",
        )

    def test_specification_meta_imports_the_toolchain(self):
        tree: dict[str, list[str] | str] = dict(GOOD)
        tree["EthLib.Base.A"] = "module\n\npublic meta import Lean.Elab.Command\n"
        self.assert_fails(tree, "a specification never uses `meta import`")

    def test_export_meta_imports_a_property_that_reaches_the_specification(self):
        tree: dict[str, list[str] | str] = dict(with_imports("EthLib.Exports"))
        # The property imports only the specification, so no other rule applies.
        tree["EthLib.Execution.Proofs.A"] = ["EthLib.Execution.A"]
        tree["EthLib.Execution.Exports.A"] = (
            "module\n\npublic import EthLib.Execution.A\n"
            "public meta import EthLib.Execution.Proofs.A\n"
        )
        self.assert_fails(tree, "meta-imports EthLib.Execution.Proofs.A")

    def test_export_meta_imports_the_toolchain(self):
        tree: dict[str, list[str] | str] = dict(with_imports("EthLib.Exports"))
        tree["EthLib.Execution.Exports.A"] = (
            "module\n\npublic import EthLib.Execution.A\npublic meta import Lean.Elab.Command\n"
        )
        self.assertEqual(Tree(tree).problems(), [])

    def test_export_meta_imports_an_export_of_the_toolchain(self):
        # As `derive_py` would be, if its module imported only the toolchain.
        tree: dict[str, list[str] | str] = dict(
            with_imports("EthLib.Exports", "EthLib.Execution.Exports.Derive")
        )
        tree["EthLib.Execution.Exports.Derive"] = ["Lean.Elab.Command"]
        tree["EthLib.Execution.Exports.A"] = (
            "module\n\npublic import EthLib.Execution.A\n"
            "public meta import EthLib.Execution.Exports.Derive\n"
        )
        self.assertEqual(Tree(tree).problems(), [])

    def test_property_meta_imports_the_specification(self):
        # No export reaches the property, so its elaboration never runs inside an export.
        tree: dict[str, list[str] | str] = dict(with_imports("EthLib.Proofs"))
        tree["EthLib.Execution.Proofs.A"] = (
            "module\n\npublic import EthLib.Execution.A\nmeta import EthLib.Execution.A\n"
        )
        self.assertEqual(Tree(tree).problems(), [])

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
        tree["EthLib.Execution.Exports.Proofs.B"] = ["EthLib.Execution.Exports.A"]
        tree["EthLib.Execution.Exports.B"] = [
            "EthLib.Execution.A",
            "EthLib.Execution.Exports.Proofs.B",
        ]
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


REFINEMENT = "EthLib.Execution.Proofs.R"
# The direct import of the model in `MODELLED`, as the check reports it.
DIRECT = (
    f"EthLib/Execution/Proofs/R.lean: imports the model {MODEL}, "
    "but coverage/kinds.toml does not declare it a refinement module"
)


class KindsRule(unittest.TestCase):
    def problems(
        self,
        tree: Mapping[str, list[str] | str],
        refinement: list[str],
        models: list[str] | None = None,
        baseline: str = "",
    ) -> list[str]:
        declared = kinds(
            ["EthLib.Execution.Proofs.Models"] if models is None else models, refinement
        )
        return Tree(tree, kinds=declared, baseline=baseline).problems()

    def test_refinement_module_imports_a_model(self):
        self.assertEqual(self.problems(MODELLED, [REFINEMENT]), [])

    def test_property_imports_a_model(self):
        self.assertEqual(self.problems(MODELLED, []), [DIRECT])

    def test_property_reaches_a_model_through_a_refinement_module(self):
        # S imports R, which imports the model: only a direct import breaks the rule.
        self.assertEqual(self.problems(MODELLED, [REFINEMENT, "EthLib.Execution.Proofs.S"]), [])

    def test_module_of_imports_only(self):
        self.assertEqual(self.problems(with_proofs(MODEL_TREE, GATHERER), [REFINEMENT]), [])

    def test_aggregator_imports_a_model(self):
        # The aggregator has a body, so only its place among the aggregators exempts it.
        self.assertIn(MODEL, MODELLED["EthLib.Proofs"])
        self.assertEqual(self.problems(MODELLED, [REFINEMENT]), [])

    def test_model_imports_a_model(self):
        tree = with_proofs(MODEL_TREE, {"EthLib.Execution.Proofs.Models.N": [MODEL]})
        self.assertEqual(self.problems(tree, [REFINEMENT]), [])

    def test_specification_imports_a_model(self):
        tree = with_imports("EthLib.Engine.A", MODEL) | {
            k: v for k, v in MODELLED.items() if "Proofs" in k
        }
        problems = self.problems(tree, [REFINEMENT])
        self.assertEqual(
            problems,
            [
                f"EthLib/Engine/A.lean: imports {MODEL}, "
                "but a specification never imports a property"
            ],
        )

    def test_listed_import_passes(self):
        baseline = f"# Why.\nEthLib.Execution.Proofs.R {MODEL}\n"
        self.assertEqual(self.problems(MODELLED, [], baseline=baseline), [])

    def test_listed_import_of_a_refinement_module_is_stale(self):
        baseline = f"# Why.\nEthLib.Execution.Proofs.R {MODEL}\n"
        self.assertEqual(
            self.problems(MODELLED, [REFINEMENT], baseline=baseline),
            [
                f"scripts/check_layers_baseline.txt: EthLib.Execution.Proofs.R {MODEL} "
                "breaks no rule any more; remove the entry"
            ],
        )

    def test_listed_transitive_import_is_stale(self):
        baseline = "# Why.\nEthLib.Execution.Proofs.S EthLib.Execution.Proofs.R\n"
        self.assertEqual(
            self.problems(MODELLED, [REFINEMENT], baseline=baseline),
            [
                "scripts/check_layers_baseline.txt: EthLib.Execution.Proofs.S "
                "EthLib.Execution.Proofs.R breaks no rule any more; remove the entry"
            ],
        )

    def test_refinement_module_reaches_no_model(self):
        self.assertEqual(
            self.problems(MODELLED, [REFINEMENT, "EthLib.Execution.Proofs.A"]),
            [
                "coverage/kinds.toml: the refinement module EthLib.Execution.Proofs.A "
                "reaches no model"
            ],
        )

    def test_refinement_module_does_not_exist(self):
        self.assertEqual(
            self.problems(MODELLED, [REFINEMENT, "EthLib.Execution.Proofs.Gone"]),
            [
                "coverage/kinds.toml: the refinement module "
                "EthLib.Execution.Proofs.Gone does not exist"
            ],
        )

    def test_refinement_module_of_the_wrong_kind(self):
        tree = with_proofs(MODEL_TREE, GATHERER)
        cases = {
            "EthLib.Execution.A": "is not a property module",
            MODEL: "is a model",
            "EthLib.Execution.Proofs.All": "only gathers imports",
            "EthLib.Proofs": "is an aggregator",
        }
        for name, reason in cases.items():
            with self.subTest(name=name):
                self.assertEqual(
                    self.problems(tree, [REFINEMENT, name]),
                    [f"coverage/kinds.toml: the refinement module {name} {reason}"],
                )

    def test_model_matches_no_module(self):
        models = ["EthLib.Execution.Proofs.Models", "EthLib.Consensus.Proofs.Models"]
        self.assertEqual(
            self.problems(MODELLED, [REFINEMENT], models=models),
            ["coverage/kinds.toml: no module is under the model EthLib.Consensus.Proofs.Models"],
        )

    def test_model_outside_proofs(self):
        models = ["EthLib.Execution.Proofs.Models", "EthLib.Engine.A"]
        self.assertEqual(
            self.problems(MODELLED, [REFINEMENT], models=models),
            ["coverage/kinds.toml: the model EthLib.Engine.A is not under a Proofs directory"],
        )

    def test_model_prefix_matches_whole_components(self):
        # `EthLib.Execution.Proofs.Model` names no module, and is no prefix of `Models.M`.
        models = ["EthLib.Execution.Proofs.Model"]
        self.assertEqual(
            self.problems(MODELLED, [], models=models),
            ["coverage/kinds.toml: no module is under the model EthLib.Execution.Proofs.Model"],
        )

    def test_missing_file(self):
        self.assertEqual(Tree(GOOD, kinds=None).problems(), ["coverage/kinds.toml: missing"])

    def test_unreadable_file_keeps_the_baseline_of_the_rule(self):
        # Without the declarations, the check cannot tell whether the entry is still needed.
        baseline = f"# Why.\nEthLib.Execution.Proofs.R {MODEL}\n"
        cases = {None: r"missing", "models = [": r"not valid TOML: .+"}
        for declared, message in cases.items():
            with self.subTest(declared=declared):
                problems = Tree(MODELLED, kinds=declared, baseline=baseline).problems()
                self.assertEqual(len(problems), 1, problems)
                self.assertRegex(problems[0], f"^coverage/kinds\\.toml: {message}$")

    def test_invalid_file_is_reported(self):
        problems = Tree(GOOD, kinds='models = []\nrefinement = "EthLib.Proofs"\n').problems()
        self.assertEqual(
            problems,
            ["coverage/kinds.toml: refinement must be a list of module names, each a string"],
        )


class DirectoryCycles(unittest.TestCase):
    def cycle(self, *directories: str) -> dict[str, list[str]]:
        """A cycle of directory imports without a cycle between individual Lean modules."""
        return {
            f"EthLib.Execution.{source}.{module}": imported
            for source, target in zip(directories, (*directories[1:], directories[0]), strict=True)
            for module, imported in (("Use", [f"EthLib.Execution.{target}.Types"]), ("Types", []))
        }

    def test_acyclic_directories(self):
        graph = self.cycle("A", "B", "C")
        graph["EthLib.Execution.C.Use"] = []
        self.assertEqual(layers.directory_cycles(graph), [])

    def test_two_directories(self):
        graph = self.cycle("A", "B")
        self.assertEqual(
            layers.directory_cycles(graph),
            [
                (
                    "EthLib.Execution.A.Use",
                    "EthLib.Execution.B.Types",
                    ("EthLib.Execution.A", "EthLib.Execution.B", "EthLib.Execution.A"),
                ),
                (
                    "EthLib.Execution.B.Use",
                    "EthLib.Execution.A.Types",
                    ("EthLib.Execution.B", "EthLib.Execution.A", "EthLib.Execution.B"),
                ),
            ],
        )

    def test_indirect_cycle(self):
        graph = self.cycle("A", "B", "C")
        problems = layers.directory_cycles(graph)
        self.assertEqual(len(problems), 3)
        self.assertEqual(
            problems[0][2],
            (
                "EthLib.Execution.A",
                "EthLib.Execution.B",
                "EthLib.Execution.C",
                "EthLib.Execution.A",
            ),
        )

    def test_nested_directories(self):
        self.assertEqual(len(layers.directory_cycles(self.cycle("Evm.Gas", "Evm.Machine"))), 2)

    def test_ancestor_projection(self):
        # The nearest directories alone have no cycle: A.Sub1 -> B -> A.Sub2.
        graph = {
            "EthLib.Execution.A.Sub1.Use": ["EthLib.Execution.B.Types"],
            "EthLib.Execution.A.Sub2.Types": [],
            "EthLib.Execution.B.Use": ["EthLib.Execution.A.Sub2.Types"],
            "EthLib.Execution.B.Types": [],
        }
        self.assertEqual(len(layers.directory_cycles(graph)), 2)

    def test_root_file_imports(self):
        graph = {
            "EthLib.Execution.A": ["EthLib.Execution.B.Types"],
            "EthLib.Execution.A.Types": [],
            "EthLib.Execution.B.Use": ["EthLib.Execution.A.Types"],
            "EthLib.Execution.B.Types": [],
        }
        self.assertEqual(len(layers.directory_cycles(graph)), 2)

    def test_imported_root_file(self):
        graph = {
            "EthLib.Execution.A.Use": ["EthLib.Execution.B"],
            "EthLib.Execution.A.Types": [],
            "EthLib.Execution.B": ["EthLib.Execution.A.Types"],
            "EthLib.Execution.B.Types": [],
        }
        self.assertEqual(len(layers.directory_cycles(graph)), 2)

    def test_root_directory_with_only_a_readme(self):
        for component, library in (
            ("", "EthLib"),
            ("Proofs.", "EthLib.Proofs"),
            ("Exports.", "EthLib.Exports"),
        ):
            with self.subTest(component=component):
                prefix = f"EthLib.Execution.{component}"
                graph: dict[str, list[str]] = {
                    prefix + "A": [prefix + "B.Types"],
                    prefix + "B.Use": [prefix + "A"],
                    prefix + "B.Types": [],
                }
                modules = {name: list(imported) for name, imported in GOOD.items()} | graph
                modules[library] += list(graph)
                tree = Tree(modules)
                self.addCleanup(tree.tmp.cleanup)
                # Without a matching directory, A.lean belongs to its parent.
                self.assertEqual(layers.check(tree.root), [])
                folder = tree.root.joinpath("EthLib", "Execution", *component.split(".")[:-1])
                directory = folder / "A"
                directory.mkdir()
                (directory / "README.md").write_text("# A\n", encoding="utf-8")
                path = folder.relative_to(tree.root).as_posix()
                problems = layers.check(tree.root)
                self.assertEqual(
                    problems,
                    [
                        f"{path}/A.lean:3: imports {prefix}B.Types, "
                        f"which forms a directory cycle: {path}/A/ -> {path}/B/ -> {path}/A/",
                        f"{path}/B/Use.lean:3: imports {prefix}A, "
                        f"which forms a directory cycle: {path}/B/ -> {path}/A/ -> {path}/B/",
                    ],
                )

    def test_acyclic_root_directory_with_only_a_readme(self):
        graph = {
            "EthLib.Execution.A": ["EthLib.Execution.B.Types"],
            "EthLib.Execution.B.Types": [],
        }
        tree = Tree(with_modules(graph))
        self.addCleanup(tree.tmp.cleanup)
        directory = tree.root / "EthLib/Execution/A"
        directory.mkdir()
        (directory / "README.md").write_text("# A\n", encoding="utf-8")
        self.assertEqual(layers.check(tree.root), [])

    def test_flat_file_without_a_directory(self):
        graph = {
            "EthLib.Execution.Flat": ["EthLib.Execution.A.Types"],
            "EthLib.Execution.A.Use": ["EthLib.Execution.Flat"],
            "EthLib.Execution.A.Types": [],
        }
        self.assertEqual(layers.directory_cycles(graph), [])

    def test_parent_and_child_directories(self):
        self.assertEqual(layers.directory_cycles(self.cycle("A", "A.Child")), [])

    def test_same_directory(self):
        self.assertEqual(layers.directory_cycles(self.cycle("A")), [])

    def test_directory_names_with_a_common_prefix(self):
        self.assertEqual(len(layers.directory_cycles(self.cycle("Foo", "Foobar"))), 2)

    def test_literal_dots_are_not_directory_separators(self):
        graph = self.cycle("A", "«A.B»")
        self.assertEqual(len(layers.directory_cycles(graph)), 2)
        problems = Tree(with_modules(graph)).problems()
        self.assertEqual(len(problems), 2)
        self.assertTrue(any("EthLib/Execution/A.B/Use.lean:3:" in item for item in problems))

    def test_quoted_directory_with_spaces(self):
        graph = self.cycle("A", "«B C»")
        self.assertEqual(len(Tree(with_modules(graph)).problems()), 2)

    def test_root_file_with_a_literal_dot(self):
        graph = {
            "EthLib.Execution.A.Use": ["EthLib.Execution.«A.B»"],
            "EthLib.Execution.A.Types": [],
            "EthLib.Execution.«A.B»": ["EthLib.Execution.A.Types"],
            "EthLib.Execution.«A.B».Types": [],
        }
        problems = Tree(with_modules(graph)).problems()
        self.assertEqual(len(problems), 2)
        self.assertTrue(any("EthLib/Execution/A.B.lean:3:" in item for item in problems))

    def test_properties_and_exports_are_checked(self):
        for part in ("Proofs", "Exports"):
            with self.subTest(part=part):
                self.assertEqual(
                    len(layers.directory_cycles(self.cycle(f"{part}.A", f"{part}.B"))), 2
                )
                graph = self.cycle("A", f"{part}.B")
                self.assertEqual(len(layers.directory_cycles(graph)), 2)

    def test_cycle_between_properties_and_exports(self):
        graph = self.cycle("Proofs.A", "Exports.B")
        self.assertEqual(len(layers.directory_cycles(graph)), 2)

    def test_cycle_through_all_three_kinds(self):
        graph = self.cycle("A", "Proofs.B", "Exports.C")
        self.assertEqual(len(layers.directory_cycles(graph)), 3)

    def test_different_layers_are_excluded(self):
        graph = {
            name.replace("Execution.B", "Consensus.B"): [
                imported.replace("Execution.B", "Consensus.B") for imported in imports
            ]
            for name, imports in self.cycle("A", "B").items()
        }
        self.assertEqual(layers.directory_cycles(graph), [])

    def test_unknown_target_is_excluded(self):
        graph = self.cycle("A", "B")
        del graph["EthLib.Execution.B.Types"]
        self.assertEqual(layers.directory_cycles(graph), [])

    def test_diagnostics_are_deterministic(self):
        graph = self.cycle("A", "B", "C")
        graph["EthLib.Execution.A.Use"] += ["EthLib.Execution.C.Types"] * 2
        reversed_graph = {
            name: list(reversed(imports)) for name, imports in reversed(graph.items())
        }
        self.assertEqual(layers.directory_cycles(graph), layers.directory_cycles(reversed_graph))
        self.assertEqual(len(layers.directory_cycles(graph)), 4)

    def test_diagnostic_names_the_import_and_cycle(self):
        problems = Tree(with_modules(self.cycle("A", "B"))).problems()
        self.assertEqual(len(problems), 2)
        self.assertEqual(
            problems[0],
            "EthLib/Execution/A/Use.lean:3: imports EthLib.Execution.B.Types, "
            "which forms a directory cycle: EthLib/Execution/A/ -> EthLib/Execution/B/ -> "
            "EthLib/Execution/A/",
        )

    def test_baseline_allows_existing_cycle(self):
        baseline = (
            "# Shared types await a move.\n"
            "EthLib.Execution.A.Use EthLib.Execution.B.Types\n"
            "EthLib.Execution.B.Use EthLib.Execution.A.Types\n"
        )
        self.assertEqual(Tree(with_modules(self.cycle("A", "B")), baseline=baseline).problems(), [])

    def test_new_import_in_an_existing_cycle_fails(self):
        graph = self.cycle("A", "B")
        graph["EthLib.Execution.A.More"] = ["EthLib.Execution.B.Types"]
        baseline = (
            "EthLib.Execution.A.Use EthLib.Execution.B.Types\n"
            "EthLib.Execution.B.Use EthLib.Execution.A.Types\n"
        )
        problems = Tree(with_modules(graph), baseline=baseline).problems()
        self.assertEqual(len(problems), 1)
        self.assertIn("EthLib/Execution/A/More.lean:3: imports", problems[0])
        self.assertIn("directory cycle", problems[0])

    def test_baseline_is_stale_after_breaking_the_cycle(self):
        graph = self.cycle("A", "B")
        graph["EthLib.Execution.B.Use"] = []
        baseline = "EthLib.Execution.A.Use EthLib.Execution.B.Types\n"
        self.assertEqual(
            Tree(with_modules(graph), baseline=baseline).problems(),
            [
                "scripts/check_layers_baseline.txt: EthLib.Execution.A.Use "
                "EthLib.Execution.B.Types breaks no rule any more; remove the entry"
            ],
        )


class ReadKinds(unittest.TestCase):
    def test_valid(self):
        self.assertEqual(
            layers.read_kinds('models = ["A"]\nrefinement = ["B", "C"]\n'),
            layers.Kinds(models=("A",), refinement=("B", "C")),
        )

    def test_invalid(self):
        cases = {
            "models = [": r"not valid TOML: .+",
            'models = []\nrefinement = []\nrefinements = ["A"]\n': (
                r"unknown keys \['refinements'\]; the file holds only \['models', 'refinement'\]"
            ),
            "models = []\n": r"the key refinement is missing",
            'models = "A"\nrefinement = []\n': (
                r"models must be a list of module names, each a string"
            ),
            'models = ["A", 1]\nrefinement = []\n': (
                r"models must be a list of module names, each a string"
            ),
            'models = []\nrefinement = ["A", "B", "A"]\n': (
                r"refinement lists \['A'\] more than once"
            ),
        }
        for text, message in cases.items():
            with self.subTest(text=text), self.assertRaisesRegex(layers.KindsError, f"^{message}$"):
                layers.read_kinds(text)


class Header(unittest.TestCase):
    def test_literal_dots_in_module_names(self):
        path = Path("EthLib/Execution/A.B/Types.lean")
        self.assertEqual(layers.module_name(path, Path(".")), "EthLib.Execution.«A.B».Types")
        self.assertEqual(
            layers.imports("module\npublic import EthLib.Execution.«A.B».Types\n"),
            ["EthLib.Execution.«A.B».Types"],
        )

    def test_quoted_import_with_spaces_keeps_later_imports(self):
        self.assertEqual(
            layers.imports(
                "module\npublic import EthLib.Execution.«A B».Types\n"
                "public import EthLib.Execution.C.Types\n"
            ),
            ["EthLib.Execution.«A B».Types", "EthLib.Execution.C.Types"],
        )

    def test_import_forms(self):
        text = (
            "/- import EthLib.Commented -/\nmodule\n\n-- import EthLib.Line\n"
            "public import EthLib.A\nimport all EthLib.B\n/- between -/\nmeta import EthLib.C\n"
            "public meta import «EthLib».D\nimport EthLib.E\n\n/-! import EthLib.Doc -/\n"
        )
        self.assertEqual(
            layers.imports(text), ["EthLib.A", "EthLib.B", "EthLib.C", "EthLib.D", "EthLib.E"]
        )

    def test_meta_imports(self):
        text = (
            "module\n\npublic import EthLib.A\npublic meta import EthLib.B\n"
            "meta import all EthLib.C\n"
        )
        self.assertEqual(
            layers.header_imports(text),
            [("EthLib.A", False, 3), ("EthLib.B", True, 4), ("EthLib.C", True, 5)],
        )

    def test_header_ends_at_the_first_command(self):
        self.assertEqual(layers.imports("module\nimport A\ndef x := 1\nimport B\n"), ["A"])

    def test_code_after_the_header(self):
        imported, rest = layers.read_header("module\nimport A\n-- note\ndef x := 1\n")
        self.assertEqual([item.module for item in imported], ["A"])
        self.assertEqual(rest.strip(), "def x := 1")
        self.assertEqual(layers.read_header("module\nimport A\n/- only -/\n")[1].strip(), "")

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
