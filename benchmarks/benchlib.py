"""Timing and output digests shared by the three harnesses."""

import gc
import hashlib
import json
import os
import statistics
import sys
import time
import traceback
from pathlib import Path

ONLY = set(os.environ.get("BENCH_ONLY", "").split(",")) - {""}
SKIP = set(os.environ.get("BENCH_SKIP", "").split(",")) - {""}
# Seconds that one repeat should last, and the number of repeats.
BUDGET = float(os.environ.get("BENCH_BUDGET", "0.3"))
REPEATS = int(os.environ.get("BENCH_REPEATS", "5"))
# A row whose first call takes longer than this many seconds is timed once.
SLOW_CAP = float(os.environ.get("BENCH_SLOW_CAP", "900"))


def canon(x) -> bytes:
    """A byte form of an output that is equal on two sides exactly when the values are."""
    if isinstance(x, (bytes, bytearray, memoryview)):
        return b"B" + bytes(x).hex().encode()
    if isinstance(x, bool):
        return b"T" if x else b"F"
    if isinstance(x, int):
        return b"I" + str(int(x)).encode()
    if isinstance(x, (list, tuple)):
        return b"[" + b",".join(canon(y) for y in x) + b"]"
    if x is None:
        return b"N"
    raise TypeError(type(x))


def digest(x) -> str:
    """The digest of an output that compare.py checks across the sides."""
    return hashlib.sha256(canon(x)).hexdigest()[:16]


class Runner:
    """Time named rows and save the results of one side to a JSON file."""

    def __init__(self, side: str, out_path: str):
        """Record the side and the output path, with no results yet."""
        self.side = side
        self.out_path = out_path
        self.results = {}

    def run(self, name: str, fn, norm=lambda r: r, budget: float | None = None):
        """Time one row; `norm` maps the output to the form both sides agree on."""
        if (ONLY and name not in ONLY) or name in SKIP:
            return
        budget = BUDGET if budget is None else budget
        try:
            start = time.perf_counter()
            out = fn()
            first = time.perf_counter() - start
            out_digest = digest(norm(out))
            if first > SLOW_CAP:
                times, n = [first], 1
            else:
                n = max(1, int(budget / max(first, 1e-7)))
                repeats = REPEATS if first * n * REPEATS < 120 else 2
                times = []
                for _ in range(repeats):
                    gc.collect()
                    gc.disable()
                    start = time.perf_counter()
                    for _ in range(n):
                        fn()
                    times.append((time.perf_counter() - start) / n)
                    gc.enable()
            self.results[name] = {
                "best": min(times),
                "median": statistics.median(times),
                "worst": max(times),
                "n": n,
                "repeats": len(times),
                "first": first,
                "out": out_digest,
            }
            print(
                f"{self.side:8} {name:40} best {min(times) * 1e6:14.1f} us  "
                f"spread {max(times) / min(times):5.2f}  out {out_digest}",
                flush=True,
            )
        except Exception as e:  # report the row and go on with the next one
            self.results[name] = {"error": f"{type(e).__name__}: {e}"[:300]}
            print(f"{self.side:8} {name:40} ERROR {type(e).__name__}: {e}"[:300], flush=True)
            if os.environ.get("BENCH_TRACE"):
                traceback.print_exc()
        self.save()

    def save(self):
        """Write the results so far."""
        meta = {
            "side": self.side,
            "python": sys.version,
            "load": os.getloadavg(),
            "time": time.strftime("%Y-%m-%dT%H:%M:%S"),
        }
        with open(self.out_path, "w") as f:
            json.dump({"meta": meta, "results": self.results}, f, indent=1)


def load(data_dir: str, name: str):
    """Read one input file of the data directory."""
    return json.loads((Path(data_dir) / name).read_text())
