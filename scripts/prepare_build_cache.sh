#!/usr/bin/env bash
# actions/toolkit, packages/cache/src/internal/cacheUtils.ts, `resolvePaths`:
# a selected parent directory is archived recursively, despite child glob exclusions.
# Lake recreates setup files for each build; their absolute runner paths must not be cached.
# Checker binaries in `bin/` are not default targets and add over 1 GiB to the cache.
set -euo pipefail
build_dir="${1:-.lake/build}"
find "$build_dir" \( -name '*.setup.json' -o -name '*.irsetup.json' \) ! -type d -delete
rm -rf "$build_dir/bin"
