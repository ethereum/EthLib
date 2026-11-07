#!/usr/bin/env bash
# Replay every declaration of EthLib into Lean's kernel with leanchecker.
# Run it after `lake build`, which writes the `.olean` files that it reads.
#
# leanchecker replays the private part of each module, so it checks proof bodies again.
# It finds a declaration that a metaprogram added without the kernel check.
# It uses the same kernel as Lean, so it does not check the kernel itself.
#
# leanchecker replays every module whose name starts with its argument, in one process.
# Each replay loads all imports of its module, Mathlib included, and the process keeps that
# memory until it exits: one call for a whole layer reached 15 GB on the 16 GB runner.
# So the script replays each module in its own process, `REPLAY_JOBS` at a time.
set -euo pipefail
cd "$(dirname "$0")/.."

# First, leanchecker must reject a theorem that the kernel never checked.
fixture_dir="$(mktemp -d)"
trap 'rm -rf "$fixture_dir"' EXIT
lake env lean -o "$fixture_dir/ReplayFixture.olean" scripts/ReplayFixture.lean
if lake env bash -c 'LEAN_PATH="$1:$LEAN_PATH" leanchecker ReplayFixture' _ "$fixture_dir" \
    > "$fixture_dir/fixture.log" 2>&1; then
  cat "$fixture_dir/fixture.log"
  echo "leanchecker accepted a theorem that the kernel never checked" >&2
  exit 1
fi
# A failure for another reason, such as a missing leanchecker, must not pass for a rejection.
expected="while replaying declaration 'ReplayFixture.unchecked'"
if ! grep -q "$expected" "$fixture_dir/fixture.log"; then
  cat "$fixture_dir/fixture.log"
  echo "leanchecker failed on the fixture for another reason" >&2
  exit 1
fi
echo "leanchecker rejects the unchecked fixture theorem"

# A restored build cache can hold the files of a module whose source is gone.
# leanchecker replays every module under the name that it gets, so it would replay such a module.
# Its imports may have changed, so remove its files first.
find .lake/build/lib/lean/EthLib -name '*.olean' | while read -r olean; do
  source="${olean#.lake/build/lib/lean/}"
  if [ ! -f "${source%.olean}.lean" ]; then
    echo "removing the build of a deleted module: ${olean%.olean}"
    rm -f "${olean%.olean}".*
  fi
done

# A module that only imports declares nothing, so it is not replayed.
# A module with other content and submodules is replayed with its submodules.
jobs="${REPLAY_JOBS:-2}"
modules="$(mktemp)"
targets="$(mktemp)"
trap 'rm -rf "$fixture_dir" "$modules" "$targets"' EXIT
find EthLib -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | LC_ALL=C sort > "$modules"
while read -r m; do
  if grep -q "^${m//./\\.}\\." "$modules"; then
    file="$(echo "$m" | tr . /).lean"
    # Comments, imports, sections and commands such as `#print` declare nothing.
    # One awk reads the whole file, so no pipe can end early.
    if awk '
        { line = $0 }
        inner { k = index(line, "-/"); if (!k) next; line = substr(line, k + 2); inner = 0 }
        { while ((k = index(line, "/-")) > 0) {
            rest = substr(line, k + 2); e = index(rest, "-/")
            if (e) line = substr(line, 1, k - 1) substr(rest, e + 2)
            else { line = substr(line, 1, k - 1); inner = 1 } } }
        { sub(/--.*/, "", line) }
        line ~ /^[ \t]*$/ { next }
        line ~ /^[ \t]*(module|end|(@\[expose\] )?(public )?section)([ \t]|$)/ { next }
        line ~ /^[ \t]*(public )?import / { next }
        line ~ /^[ \t]*(namespace|open) / { next }
        line ~ /^[ \t]*#[a-z_]+/ { next }
        { found = 1; exit }
        END { exit !found }' "$file"; then
      echo "$m" >> "$targets"
    fi
  else
    echo "$m" >> "$targets"
  fi
done < "$modules"
echo "replaying $(wc -l < "$targets") of $(wc -l < "$modules") modules, $jobs at a time"
start=$SECONDS
# A proof can make the kernel evaluate a large computation that the build did not evaluate.
# Its replay can then run for hours and fill the memory of the runner.
# So each module has a time budget, and a module that exceeds it fails the replay by name.
budget="${REPLAY_BUDGET:-300}"
# `xargs` runs every module and fails if one fails.
# leanchecker names the module that it rejects.
LEAN_NUM_THREADS=1 lake env xargs -P "$jobs" -n 1 bash -c '
  begin=$SECONDS
  status=0
  timeout "$1" leanchecker "$2" || status=$?
  if [ "$status" -eq 0 ]; then
    echo "$2 replayed in $((SECONDS - begin)) s"
  elif [ "$status" -eq 124 ]; then
    echo "$2 did not replay within the budget of $1 s" >&2
  else
    echo "$2 failed to replay after $((SECONDS - begin)) s" >&2
  fi
  exit "$((status != 0))"' _ "$budget" < "$targets"
echo "replayed in $((SECONDS - start)) s"
