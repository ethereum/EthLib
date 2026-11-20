#!/usr/bin/env bash
# Replay every declaration of EthLib into Lean's kernel with the replay function of leanchecker.
# Run it after `lake build`, which writes the `.olean` files that it reads.
#
# The replay reads the private part of each module, so it checks proof bodies again.
# It finds a declaration that a metaprogram added without the kernel check.
# It uses the same kernel as Lean, so it does not check the kernel itself.
#
# leanchecker replays every module whose name starts with its argument, in one process.
# With more than one such module, leanchecker from Lean v4.36.0 crashes.
# So `scripts/ReplayModule.lean` calls its replay on one module alone.
# Each replay loads all imports of its module, Mathlib included, and the process keeps that
# memory until it exits: one call for a whole layer reached 15 GB on the 16 GB runner.
# So the script replays each module in its own process, `REPLAY_JOBS` at a time.
set -euo pipefail
cd "$(dirname "$0")/.."

# First, the replay must reject a theorem that the kernel never checked.
fixture_dir="$(mktemp -d)"
trap 'rm -rf "$fixture_dir"' EXIT
lake env lean -o "$fixture_dir/ReplayFixture.olean" scripts/ReplayFixture.lean
if lake env bash -c \
    'LEAN_PATH="$1:$LEAN_PATH" REPLAY_MODULE=ReplayFixture lean scripts/ReplayModule.lean' \
    _ "$fixture_dir" > "$fixture_dir/fixture.log" 2>&1; then
  cat "$fixture_dir/fixture.log"
  echo "the replay accepted a theorem that the kernel never checked" >&2
  exit 1
fi
# A failure for another reason, such as a missing LeanChecker module, must not pass for a rejection.
expected="while replaying declaration 'ReplayFixture.unchecked'"
if ! grep -q "$expected" "$fixture_dir/fixture.log"; then
  cat "$fixture_dir/fixture.log"
  echo "the replay failed on the fixture for another reason" >&2
  exit 1
fi
echo "the replay rejects the unchecked fixture theorem"

# A module that only imports declares nothing, so it is not replayed.
# Any other module is replayed alone, and each of its submodules in its own process.
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
# The kernel names the declaration that it rejects.
LEAN_NUM_THREADS=1 lake env xargs -P "$jobs" -n 1 bash -c '
  begin=$SECONDS
  status=0
  REPLAY_MODULE="$2" timeout "$1" lean scripts/ReplayModule.lean || status=$?
  if [ "$status" -eq 0 ]; then
    echo "$2 replayed in $((SECONDS - begin)) s"
  elif [ "$status" -eq 124 ]; then
    echo "$2 did not replay within the budget of $1 s" >&2
  else
    echo "$2 failed to replay after $((SECONDS - begin)) s" >&2
  fi
  exit "$((status != 0))"' _ "$budget" < "$targets"
echo "replayed in $((SECONDS - start)) s"
