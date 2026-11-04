#!/usr/bin/env bash
# Replay every declaration of EthLib into Lean's kernel with leanchecker.
# Run it after `lake build`, which writes the `.olean` files that it reads.
#
# leanchecker replays the private part of each module, so it checks proof bodies again.
# It finds a declaration that a metaprogram added without the kernel check.
# It uses the same kernel as Lean, so it does not check the kernel itself.
#
# leanchecker replays all modules of a prefix in parallel, and each replay loads all imports
# of its module. So the script replays one layer at a time, and `LEAN_NUM_THREADS` caps the
# number of parallel replays.
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

# The library roots only import, so the layers under them hold every declaration.
for dir in EthLib/*/; do
  prefix="EthLib.$(basename "$dir")"
  echo "::group::$prefix"
  start=$SECONDS
  lake env leanchecker "$prefix"
  echo "$prefix: replayed in $((SECONDS - start)) s"
  echo "::endgroup::"
done
