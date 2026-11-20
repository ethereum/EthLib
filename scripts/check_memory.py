"""Report the time, CPU time and peak memory that Lean needs to elaborate each given file."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

GIB = 1024**3
DEFAULT_WARN_GIB = 4.0
DEFAULT_FAIL_GIB = 6.0


def measure(path: str) -> tuple[float, float, int, int]:
    """Elaborate one file, and return its seconds, CPU seconds, peak bytes and exit code."""
    start = time.monotonic()
    # Lean's messages go to stderr, so that stdout holds only the report.
    process = subprocess.Popen(["lake", "env", "lean", path], stdout=sys.stderr)
    # The resource usage of this child alone, which includes the Lean process that it waited for.
    # Linux gives the peak resident set size in KiB.
    _, status, usage = os.wait4(process.pid, 0)
    seconds = time.monotonic() - start
    # The CPU time counts user and system time, of the Lean process too.
    cpu = usage.ru_utime + usage.ru_stime
    return seconds, cpu, usage.ru_maxrss * 1024, os.waitstatus_to_exitcode(status)


def classify(
    peak: int, cpu: float, exit_code: int, warn: int, fail: int, fail_cpu: float | None = None
) -> str:
    """Return the result of one file: `ok`, `warning`, `failure` or `error`."""
    # Either limit fails the file, and the CPU limit applies only when it is given.
    if exit_code != 0:
        return "error"
    if peak > fail or (fail_cpu is not None and cpu > fail_cpu):
        return "failure"
    if peak > warn:
        return "warning"
    return "ok"


def main(argv: list[str] | None = None) -> int:
    """Measure each file, print the table and the annotations, and return the exit code."""
    parser = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    # Lean reads the imports of each file from their `.olean` files, so they must be built.
    parser.add_argument("files", nargs="*", help="Lean files to elaborate")
    parser.add_argument("--warn-gib", type=float, default=DEFAULT_WARN_GIB)
    parser.add_argument("--fail-gib", type=float, default=DEFAULT_FAIL_GIB)
    parser.add_argument("--fail-cpu-seconds", type=float, help="fail a file above this CPU time")
    parser.add_argument("--summary", type=Path, help="append the Markdown table to this file")
    args = parser.parse_args(argv)

    warn = int(args.warn_gib * GIB)
    fail = int(args.fail_gib * GIB)

    limits = f"warning above {args.warn_gib:g} GiB, failure above {args.fail_gib:g} GiB"
    if args.fail_cpu_seconds is not None:
        limits += f" or {args.fail_cpu_seconds:g} CPU seconds"
    rows = [
        f"Peak memory of each Lean file ({limits}).",
        "",
        "| File | Time (s) | CPU (s) | Peak memory (GiB) | Result |",
        "| --- | --- | --- | --- | --- |",
    ]
    failed = False
    for path in args.files:
        seconds, cpu, peak, exit_code = measure(path)
        result = classify(peak, cpu, exit_code, warn, fail, args.fail_cpu_seconds)
        rows.append(f"| `{path}` | {seconds:.1f} | {cpu:.1f} | {peak / GIB:.2f} | {result} |")
        # GitHub turns these lines into annotations on the file.
        if result == "warning":
            print(f"::warning file={path}::{path} needs {peak / GIB:.2f} GiB to elaborate")
        elif result == "failure":
            print(
                f"::error file={path}::{path} needs {peak / GIB:.2f} GiB "
                f"and {cpu:.1f} CPU seconds to elaborate"
            )
        elif result == "error":
            print(f"::error file={path}::Lean exited with code {exit_code} on {path}")
        failed |= result in ("failure", "error")

    if not args.files:
        rows.append("| No Lean file | | | | |")
    report = "\n".join(rows) + "\n"
    print(report, end="")
    if args.summary is not None:
        with args.summary.open("a") as summary:
            summary.write(report)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
