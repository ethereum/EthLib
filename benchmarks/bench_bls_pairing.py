"""Time BLS pairing and verification on the pinned verification vectors."""

import json
import os
import platform
import sys
from pathlib import Path


def main() -> None:
    """Load one build, check the vectors and time ten valid cases per call."""
    package_root, fixture_root, output = map(Path, sys.argv[1:4])
    sys.path.insert(0, str(package_root))
    sys.path.insert(0, str(fixture_root / "benchmarks"))

    from benchlib import Runner
    from ruamel.yaml import YAML

    import ethlib
    from ethlib.cryptography import bls

    if Path(ethlib.__file__).resolve().parent != (package_root / "ethlib").resolve():
        raise ValueError("imported package is not the requested build")

    loader = YAML(typ="safe", pure=True)
    paths = sorted((fixture_root / "tests/cryptography/bls/verify").glob("*/data.yaml"))
    cases = [loader.load(path.read_text()) for path in paths]
    assert len(cases) == 29
    inputs = []
    for case in cases:
        row = case["input"]
        args = tuple(
            bytes.fromhex(row[k].removeprefix("0x")) for k in ("pubkey", "message", "signature")
        )
        assert bls.verify(*args) is case["output"]
        if case["output"]:
            inputs.append(args)
    assert len(inputs) == 10

    affinity = None
    if hasattr(os, "sched_getaffinity"):
        affinity = sorted(os.sched_getaffinity(0))
        for thread in Path("/proc/self/task").iterdir():
            assert sorted(os.sched_getaffinity(int(thread.name))) == affinity

    pairing_outputs = [bls.pairing(pk, sig) for pk, _, sig in inputs]
    runner = Runner(output.stem, str(output))
    runner.run("pairing", lambda: [bls.pairing(pk, sig) for pk, _, sig in inputs])
    runner.run("verify", lambda: [bls.verify(pk, msg, sig) for pk, msg, sig in inputs])
    report = json.loads(output.read_text())
    report["meta"].update(
        {
            "platform": platform.platform(),
            "package": str(Path(ethlib.__file__).resolve()),
            "inputs_per_call": len(inputs),
            "checked_verify_cases": len(cases),
            "affinity": affinity,
        }
    )
    report["pairing_outputs"] = [value.hex() for value in pairing_outputs]
    if any("error" in row for row in report["results"].values()):
        raise ValueError("benchmark operation failed")
    output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
