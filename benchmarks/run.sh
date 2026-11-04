#!/usr/bin/env bash
# Run the three harnesses in turn, each pinned to one core, and print the merged table.
#
#     benchmarks/run.sh            # 3 rounds on core 0
#     ROUNDS=1 CORE=6 benchmarks/run.sh
#
# Run setup.sh first, and build the bindings with `uv sync --extra test` at the repository root.
# BENCH_ONLY and BENCH_SKIP take comma-separated row names; benchlib.py reads them.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
DATA=$HERE/data
OUT=${OUT:-$HERE/results}
CORE=${CORE:-0}
ROUNDS=${ROUNDS:-3}
ETHLIB_PY=${ETHLIB_PY:-$ROOT/.venv/bin/python}
EXEC_PY=$HERE/refs/execution-specs/.venv/bin/python
CONS_PY=$HERE/refs/consensus-specs/.venv/bin/python

mkdir -p "$OUT"
for r in $(seq 1 "$ROUNDS"); do
  echo "round $r $(date +%T) load $(cut -d' ' -f1-3 /proc/loadavg)"
  taskset -c "$CORE" "$ETHLIB_PY" -u "$HERE/bench_ethlib.py" "$DATA" "$OUT/ethlib_r$r.json"
  taskset -c "$CORE" "$EXEC_PY" -u "$HERE/bench_eels.py" "$DATA" "$OUT/eels_r$r.json"
  taskset -c "$CORE" "$CONS_PY" -u "$HERE/bench_pyspec.py" "$DATA" "$OUT/pyspec_r$r.json"
done
uv run --no-project --python 3.12 python "$HERE/compare.py" "$OUT" | tee "$OUT/table.md"
