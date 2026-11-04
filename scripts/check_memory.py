"""Report the time and the peak memory that Lean needs to elaborate each given file.

CI runs this check after the build, on the Lean files that a pull request changes.
The imports of each file must be built, so that Lean reads them from their `.olean` files.

A file above the warning limit gets a warning, and a file above the failure limit fails the check.
"""

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


def measure(path: str) -> tuple[float, int, int]:
    """Elaborate one file, and return the seconds, the peak memory in bytes and the exit code."""
    start = time.monotonic()
    # Lean's messages go to stderr, so that stdout holds only the report.
    process = subprocess.Popen(["lake", "env", "lean", path], stdout=sys.stderr)
    # The resource usage of this child alone, which includes the Lean process that it waited for.
    # Linux gives the peak resident set size in KiB.
    _, status, usage = os.wait4(process.pid, 0)
    seconds = time.monotonic() - start
    return seconds, usage.ru_maxrss * 1024, os.waitstatus_to_exitcode(status)


def classify(peak: int, exit_code: int, warn: int, fail: int) -> str:
    """Return the result of one file: `ok`, `warning`, `failure` or `error`."""
    if exit_code != 0:
        return "error"
    if peak > fail:
        return "failure"
    if peak > warn:
        return "warning"
    return "ok"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="*", help="Lean files to elaborate")
    parser.add_argument("--warn-gib", type=float, default=DEFAULT_WARN_GIB)
    parser.add_argument("--fail-gib", type=float, default=DEFAULT_FAIL_GIB)
    parser.add_argument("--summary", type=Path, help="append the Markdown table to this file")
    args = parser.parse_args(argv)

    warn = int(args.warn_gib * GIB)
    fail = int(args.fail_gib * GIB)

    rows = [
        f"Peak memory of each changed Lean file (warning above {args.warn_gib:g} GiB, "
        f"failure above {args.fail_gib:g} GiB).",
        "",
        "| File | Time (s) | Peak memory (GiB) | Result |",
        "| --- | --- | --- | --- |",
    ]
    failed = False
    for path in args.files:
        seconds, peak, exit_code = measure(path)
        result = classify(peak, exit_code, warn, fail)
        rows.append(f"| `{path}` | {seconds:.1f} | {peak / GIB:.2f} | {result} |")
        # GitHub turns these lines into annotations on the file.
        if result == "warning":
            print(f"::warning file={path}::{path} needs {peak / GIB:.2f} GiB to elaborate")
        elif result == "failure":
            print(f"::error file={path}::{path} needs {peak / GIB:.2f} GiB to elaborate")
        elif result == "error":
            print(f"::error file={path}::Lean exited with code {exit_code} on {path}")
        failed |= result in ("failure", "error")

    if not args.files:
        rows.append("| No changed Lean file | | | |")
    report = "\n".join(rows) + "\n"
    print(report, end="")
    if args.summary is not None:
        with args.summary.open("a") as summary:
            summary.write(report)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
