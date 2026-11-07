"""Merge the parity counts of the shards of one suite, and check the outcomes of each row."""

# uv run --no-project --python 3.12 python scripts/merge_parity.py <report.md> <shard.json>...

import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Load the report module by path: the parity tests are no installed package.
_spec = importlib.util.spec_from_file_location(
    "report", ROOT / "bindings" / "python" / "tests" / "parity" / "report.py"
)
assert _spec and _spec.loader
report = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(report)


def main(arguments: list[str]) -> int:
    """Write the merged report, print each case count that disagrees, and return the exit code."""
    output, *inputs = arguments
    shards = [json.loads(Path(path).read_text(encoding="utf-8")) for path in inputs]
    problems = report.merge(shards) if shards else ["no shard counts"]
    if shards:
        Path(output).write_text(report.markdown() + "\n", encoding="utf-8")
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
