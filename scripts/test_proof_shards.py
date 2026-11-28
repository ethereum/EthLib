"""Unit tests for the proof sharding and disjoint artifact staging script."""

import tempfile
import unittest
from pathlib import Path

from proof_shards import (
    ROOT,
    SHARDS,
    check_partition,
    module_of_artifact,
    owner_of_module,
    shard_targets,
    stage_owner,
)


class ProofShardsTests(unittest.TestCase):
    def test_real_repository_partition_is_complete_and_disjoint(self) -> None:
        self.assertEqual(check_partition(ROOT), [])
        for shard in SHARDS:
            targets = shard_targets(ROOT, shard)
            self.assertTrue(targets, shard)
            for target in targets:
                self.assertEqual(owner_of_module(target), shard)

    def test_module_of_artifact_handles_multi_suffix_lake_files(self) -> None:
        self.assertEqual(
            module_of_artifact(Path("lib/lean/EthLib/Base/Proofs/Bytes.olean.private.hash")),
            "EthLib.Base.Proofs.Bytes",
        )
        self.assertEqual(
            module_of_artifact(Path("ir/EthLib/Base/Exports/Echo.c.o.export.trace")),
            "EthLib.Base.Exports.Echo",
        )
        self.assertEqual(module_of_artifact(Path("lib/lean/EthLib.olean")), "EthLib")
        self.assertIsNone(module_of_artifact(Path("lib/libEthLib_EthLib_Exports.a")))
        self.assertIsNone(module_of_artifact(Path("ethlib-module-times.json")))

    def test_stage_owner_produces_pairwise_disjoint_sets_and_skips_setup_and_bin(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build = root / "build"
            files = [
                "lib/lean/EthLib/Base/Bytes.olean",
                "ir/EthLib/Base/Exports/Echo.c.o.export",
                "lib/lean/EthLib/Base/Proofs/Exports/PyValue.olean",
                "lib/lean/EthLib/Base/Proofs/Bytes.olean",
                "ir/EthLib/Base/Proofs/Bytes.setup.json",
                "ir/EthLib/Base/Proofs/Bytes.irsetup.json",
                "lib/lean/EthLib/Cryptography/Proofs/Xmss/Encoding.olean",
                "lib/lean/EthLib/Cryptography/Proofs/Aes/Block.olean",
                "lib/lean/EthLib/Execution/Proofs/Blocks/DaoFork.olean",
                "lib/lean/EthLib/Consensus/Proofs/ForkChoice/Ghost.olean",
                "lib/lean/EthLib/Consensus/Proofs/Transition/Epochs.olean",
                "lib/lean/EthLib/Engine/Proofs/Jwt.olean",
                "bin/check-decls",
            ]
            for rel in files:
                path = build / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(rel)

            seen: dict[Path, str] = {}
            for owner in ("spec-exports", *SHARDS):
                out = root / f"out-{owner}"
                stage_owner(build, out, owner)
                for staged in out.rglob("*"):
                    if staged.is_dir():
                        continue
                    rel = staged.relative_to(out)
                    self.assertNotIn(rel, seen, f"overlap on {rel}")
                    self.assertFalse(rel.name.endswith(".setup.json"))
                    self.assertFalse(rel.name.endswith(".irsetup.json"))
                    self.assertNotEqual(rel.parts[0], "bin")
                    seen[rel] = owner

            self.assertEqual(seen[Path("lib/lean/EthLib/Base/Bytes.olean")], "spec-exports")
            self.assertEqual(
                seen[Path("lib/lean/EthLib/Base/Proofs/Exports/PyValue.olean")], "spec-exports"
            )
            self.assertEqual(seen[Path("lib/lean/EthLib/Base/Proofs/Bytes.olean")], "base-ser-net")
            self.assertEqual(
                seen[Path("lib/lean/EthLib/Cryptography/Proofs/Xmss/Encoding.olean")], "crypto-pq"
            )
            self.assertEqual(
                seen[Path("lib/lean/EthLib/Cryptography/Proofs/Aes/Block.olean")], "crypto-core"
            )
            self.assertEqual(
                seen[Path("lib/lean/EthLib/Execution/Proofs/Blocks/DaoFork.olean")], "execution"
            )
            self.assertEqual(
                seen[Path("lib/lean/EthLib/Consensus/Proofs/ForkChoice/Ghost.olean")],
                "consensus-forkchoice",
            )
            self.assertEqual(
                seen[Path("lib/lean/EthLib/Consensus/Proofs/Transition/Epochs.olean")],
                "consensus-rest",
            )
            self.assertNotIn(Path("lib/lean/EthLib/Engine/Proofs/Jwt.olean"), seen)


if __name__ == "__main__":
    unittest.main()
