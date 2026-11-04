#!/usr/bin/env bash
# Install the pinned reference specifications and generate the benchmark inputs.
#
#     benchmarks/setup.sh
#
# Each repository of sources.toml is cloned into benchmarks/refs/ at its commit and gets its own
# virtual environment from its own lock file. The inputs go to benchmarks/data/.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
REFS=$HERE/refs
DATA=$HERE/data
EXEC=$REFS/execution-specs
CONS=$REFS/consensus-specs

pin() {
  uv run --no-project --python 3.12 python -c \
    'import sys, tomllib; print(tomllib.load(open(sys.argv[1], "rb"))["repositories"][sys.argv[2]]["commit"])' \
    "$HERE/sources.toml" "$1"
}

checkout() {
  local repo=$1 dir=$2 commit
  commit=$(pin "$repo")
  if [ ! -d "$dir/.git" ]; then
    git init -q "$dir"
    git -C "$dir" remote add origin "https://github.com/$repo.git"
  fi
  git -C "$dir" fetch -q --depth 1 origin "$commit"
  git -C "$dir" checkout -q --detach "$commit"
}

mkdir -p "$REFS" "$DATA"
checkout ethereum/execution-specs "$EXEC"
checkout ethereum/consensus-specs "$CONS"

(cd "$EXEC" && uv sync --frozen --no-default-groups --python 3.12)
(cd "$CONS" && uv sync --frozen --all-extras --python 3.12 \
  && uv run --no-sync python -m pysetup.generate_specs --all-forks)

"$EXEC/.venv/bin/python" "$HERE/gen_inputs.py" "$ROOT" "$DATA"
"$CONS/.venv/bin/python" "$HERE/gen_cons_inputs.py" "$CONS" "$DATA"
