"""Interleave two builds on the pinned Wycheproof G2 inputs."""

import argparse
import gc
import hashlib
import json
import platform
import statistics
import subprocess
import sys
import time
from collections.abc import Callable
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VECTORS = ROOT / "bindings/python/tests/bls/wycheproof/bls_hash_to_g2_test.json"


def worker(package_root: str, passes: int) -> dict:
    """Load one build and time each operation after a warm-up pass."""
    sys.path.insert(0, package_root)
    import ethlib
    from ethlib.cryptography import bls

    if Path(ethlib.__file__).resolve().parent != (Path(package_root) / "ethlib").resolve():
        raise ValueError("imported ethlib does not belong to the requested build")

    groups = json.loads(VECTORS.read_text())["testGroups"]
    hashes = [(bytes.fromhex(t["msg"]), g["dst"].encode()) for g in groups for t in g["tests"]]
    points = [bytes.fromhex(t["expected"]) for g in groups for t in g["tests"]]
    # Toggle the compressed sign bit to exercise both roots of each nonzero point.
    points += [bytes([p[0] ^ 0x20]) + p[1:] for p in points]
    operations: dict[str, list[Callable[[], bytes]]] = {
        "decode_g2": [lambda p=p: bls.decode_g2(p) for p in points],
        "hash_to_g2": [lambda args=args: bls.hash_to_g2(*args) for args in hashes],
    }
    results = {}
    for name, calls in operations.items():
        outputs = [fn() for fn in calls]
        if name == "decode_g2" and outputs != points:
            raise ValueError("decoded points differ from their canonical encodings")
        gc.collect()
        gc.disable()
        start = time.perf_counter()
        try:
            for _ in range(passes):
                for fn in calls:
                    fn()
        finally:
            elapsed = time.perf_counter() - start
            gc.enable()
        results[name] = {
            "seconds": elapsed / (passes * len(calls)),
            "inputs": len(calls),
            "digest": hashlib.sha256(b"".join(outputs)).hexdigest(),
        }
    return results


def main() -> None:
    """Alternate the process order each round and report medians per call."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True, help="root containing the old ethlib")
    parser.add_argument("--after", type=Path, required=True, help="root containing the new ethlib")
    parser.add_argument("--rounds", type=int, default=9)
    parser.add_argument("--passes", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 2 or args.passes < 1:
        parser.error("use at least two rounds and one pass")
    roots = {"before": args.before.resolve(), "after": args.after.resolve()}
    samples = {side: [] for side in roots}
    for round_index in range(args.rounds):
        order = list(roots) if round_index % 2 == 0 else list(reversed(roots))
        for side in order:
            command = [sys.executable, __file__, "_worker", str(roots[side]), str(args.passes)]
            samples[side].append(json.loads(subprocess.check_output(command, text=True)))
    summary = {}
    for name in samples["before"][0]:
        digests = {sample[name]["digest"] for rows in samples.values() for sample in rows}
        if len(digests) != 1:
            raise ValueError(f"{name}: outputs differ between builds or rounds")
        times = {
            side: statistics.median(sample[name]["seconds"] for sample in rows)
            for side, rows in samples.items()
        }
        summary[name] = {**times, "speedup": times["before"] / times["after"]}
    report = {
        "platform": platform.platform(),
        "python": sys.version,
        "rounds": args.rounds,
        "passes": args.passes,
        "packages": {side: str(path) for side, path in roots.items()},
        "summary": summary,
        "samples": samples,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "_worker":
        print(json.dumps(worker(sys.argv[2], int(sys.argv[3]))))
    else:
        main()
