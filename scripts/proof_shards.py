"""Partition EthLib proof targets into disjoint CI shards and stage their build artifacts."""

import argparse
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

SHARDS = (
    "base-ser-net",
    "crypto-pq",
    "crypto-core",
    "execution",
    "consensus-forkchoice",
    "consensus-rest",
)

# Umbrella roots and Engine proofs are built quickly in the final `build` job after merging shards.
UNSHARDED_PROOFS = frozenset(
    {
        "EthLib.Proofs",
        "EthLib.Cryptography.Proofs",
        "EthLib.Consensus.Proofs",
    }
)

# `PythonConversions` owns `EthLib.Base.Proofs.Exports.PyValue`, which `Exports` builds in stage 1.
SPEC_EXPORTS_PROOF_MODULES = frozenset({"EthLib.Base.Proofs.Exports.PyValue"})

IMPORT_RE = re.compile(r"^(?:public\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def direct_imports(root: Path, module: str) -> list[str]:
    """The direct `EthLib.*` imports of one Lean module, in source order."""
    path = root / Path(*module.split(".")).with_suffix(".lean")
    return [
        m for m in IMPORT_RE.findall(path.read_text()) if m == "EthLib" or m.startswith("EthLib.")
    ]


def shard_targets(root: Path, shard: str) -> list[str]:
    """The Lake module targets that one proof shard builds."""
    if shard == "base-ser-net":
        return [
            "EthLib.Base.Proofs",
            "EthLib.Serialization.Proofs",
            "EthLib.Networking.Proofs",
        ]
    if shard == "crypto-pq":
        return [
            m
            for m in direct_imports(root, "EthLib.Cryptography.Proofs")
            if m.startswith("EthLib.Cryptography.Proofs.Xmss")
            or m.startswith("EthLib.Cryptography.Proofs.Sphincs")
        ]
    if shard == "crypto-core":
        return [
            m
            for m in direct_imports(root, "EthLib.Cryptography.Proofs")
            if not m.startswith("EthLib.Cryptography.Proofs.Xmss")
            and not m.startswith("EthLib.Cryptography.Proofs.Sphincs")
        ]
    if shard == "execution":
        return ["EthLib.Execution.Proofs"]
    if shard == "consensus-forkchoice":
        return [
            m
            for m in direct_imports(root, "EthLib.Consensus.Proofs")
            if m.startswith("EthLib.Consensus.Proofs.ForkChoice")
            or m.startswith("EthLib.Consensus.Proofs.DirectSafety")
        ]
    if shard == "consensus-rest":
        return [
            m
            for m in direct_imports(root, "EthLib.Consensus.Proofs")
            if not m.startswith("EthLib.Consensus.Proofs.ForkChoice")
            and not m.startswith("EthLib.Consensus.Proofs.DirectSafety")
        ]
    raise ValueError(f"unknown proof shard: {shard}")


def owner_of_module(module: str) -> str:
    """The unique build stage or proof shard that owns artifacts for `module`."""
    if module in SPEC_EXPORTS_PROOF_MODULES:
        return "spec-exports"
    if (
        module in UNSHARDED_PROOFS
        or module == "EthLib.Engine.Proofs"
        or module.startswith("EthLib.Engine.Proofs.")
    ):
        return "build"
    if module in (
        "EthLib.Base.Proofs",
        "EthLib.Serialization.Proofs",
        "EthLib.Networking.Proofs",
    ) or module.startswith(
        (
            "EthLib.Base.Proofs.",
            "EthLib.Serialization.Proofs.",
            "EthLib.Networking.Proofs.",
        )
    ):
        return "base-ser-net"
    if module.startswith(("EthLib.Cryptography.Proofs.Xmss", "EthLib.Cryptography.Proofs.Sphincs")):
        return "crypto-pq"
    if module.startswith("EthLib.Cryptography.Proofs."):
        return "crypto-core"
    if module == "EthLib.Execution.Proofs" or module.startswith("EthLib.Execution.Proofs."):
        return "execution"
    if module.startswith(
        ("EthLib.Consensus.Proofs.ForkChoice", "EthLib.Consensus.Proofs.DirectSafety")
    ):
        return "consensus-forkchoice"
    if module.startswith("EthLib.Consensus.Proofs."):
        return "consensus-rest"
    return "spec-exports"


def module_of_artifact(rel: Path) -> str | None:
    """The EthLib Lean module name for a file under `lib/lean/` or `ir/`, or `None`."""
    parts = rel.parts
    if len(parts) >= 3 and parts[0] == "lib" and parts[1] == "lean":
        sub = parts[2:]
    elif len(parts) >= 2 and parts[0] == "ir":
        sub = parts[1:]
    else:
        return None
    if not sub or sub[0].split(".")[0] != "EthLib":
        return None
    stem = sub[-1].split(".", 1)[0]
    return ".".join((*sub[:-1], stem))


def is_setup_artifact(path: Path) -> bool:
    """Whether a build file embeds runner-specific paths and must not be staged."""
    name = path.name
    return name.endswith(".setup.json") or name.endswith(".irsetup.json")


def stage_owner(build_dir: Path, out_dir: Path, owner: str) -> int:
    """Copy every build artifact owned by `owner` into `out_dir`, returning the file count."""
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)
    copied = 0
    for path in sorted(build_dir.rglob("*")):
        if path.is_dir() or is_setup_artifact(path):
            continue
        rel = path.relative_to(build_dir)
        if rel.parts[0] == "bin":
            continue
        module = module_of_artifact(rel)
        if module is None:
            # Non-module files (such as static libraries and metadata) belong to `spec-exports`.
            file_owner = "spec-exports" if rel.parts[0] in ("lib", "ir") else None
        else:
            file_owner = owner_of_module(module)
        if file_owner != owner:
            continue
        dest = out_dir / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, dest)
        copied += 1
    return copied


def check_partition(root: Path) -> list[str]:
    """Verify every proof module has one unique owner and every shard has non-empty targets."""
    problems: list[str] = []
    seen_targets: dict[str, str] = {}
    for shard in SHARDS:
        targets = shard_targets(root, shard)
        if not targets:
            problems.append(f"shard {shard} has no targets")
        for target in targets:
            if target in seen_targets:
                problems.append(
                    f"target {target} listed in both {seen_targets[target]} and {shard}"
                )
            seen_targets[target] = shard
    ethlib_dir = root / "EthLib"
    if ethlib_dir.is_dir():
        for lean in sorted(ethlib_dir.rglob("*.lean")):
            module = ".".join(lean.relative_to(root).with_suffix("").parts)
            owner = owner_of_module(module)
            if (
                ".Proofs" in module
                and owner == "spec-exports"
                and module not in SPEC_EXPORTS_PROOF_MODULES
            ):
                problems.append(f"proof module {module} fell through to spec-exports")
    return problems


def main(argv: list[str] | None = None) -> int:
    """CLI entry point for listing shard targets, staging artifacts and checking the partition."""
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    p_targets = sub.add_parser("targets", help="print Lake targets for one proof shard")
    p_targets.add_argument("shard", choices=SHARDS)
    p_targets.add_argument("--root", type=Path, default=ROOT)

    p_stage = sub.add_parser(
        "stage", help="copy one owner's build artifacts to an output directory"
    )
    p_stage.add_argument("owner", choices=("spec-exports", *SHARDS))
    p_stage.add_argument("--build-dir", type=Path, default=ROOT / ".lake" / "build")
    p_stage.add_argument("--out-dir", type=Path, required=True)

    p_check = sub.add_parser("check", help="verify disjointness and full coverage of the shards")
    p_check.add_argument("--root", type=Path, default=ROOT)

    args = parser.parse_args(argv)
    if args.command == "targets":
        print(" ".join(shard_targets(args.root, args.shard)))
        return 0
    if args.command == "stage":
        count = stage_owner(args.build_dir, args.out_dir, args.owner)
        print(f"staged {count} files for {args.owner}")
        return 0
    problems = check_partition(args.root)
    for problem in problems:
        print(f"proof_shards: {problem}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
