#!/usr/bin/env bash
# The theorem check must distinguish specification dependencies from unneeded properties.
# Its baseline must list exactly the findings, and malformed input must fail.
set -uo pipefail
cd "$(dirname "$0")/.."
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if ! lake build --wfail CheckTheoremsTest check-theorems >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures or the check do not build"
  cat "$WORK/build"
  exit 1
fi

check() {
  lake exe check-theorems --root scripts/CheckTheoremsTest "$@" 2>"$WORK/err"
}

# Names and defining modules are hand-written, independent of the checker output.
LC_ALL=C sort >"$WORK/expected" <<'END'
CheckTheoremsTest root_unused
CheckTheoremsTest.Hidden CheckTheoremsTest.Spec.private_unused
CheckTheoremsTest.PrivateDependency CheckTheoremsTest.PrivateDependency.imported_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct._proof_99
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.local_eq
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.orphan._proof_1
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.orphan.eq_1
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.private_local_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.private_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.private_with_local_definition
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.proof_local_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.removed_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.reverse_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.simp_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.sumTo_succ
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.used_only_from_exports
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.used_only_from_proofs
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.with_local_definition
CheckTheoremsTest.Spec UnrelatedNamespace.unused
END

if check --print >"$WORK/found" && diff -u "$WORK/expected" "$WORK/found"; then
  echo "ok:   every unneeded theorem is reported, and nothing else"
else
  echo "FAIL: findings differ from the planted theorems"
  cat "$WORK/err"
  FAIL=1
fi

if check --baseline "$WORK/expected" >"$WORK/out"; then
  echo "ok:   an exact baseline passes"
else
  echo "FAIL: an exact baseline fails"
  cat "$WORK/out" "$WORK/err"
  FAIL=1
fi

# Source locations support migration without making line numbers part of the baseline.
if check --list >"$WORK/list" && python3 - "$WORK/list" "$WORK/expected" <<'PY'
from pathlib import Path
import sys

listed = []
for row in Path(sys.argv[1]).read_text().splitlines():
    fields = row.split("\t")
    assert len(fields) == 5, row
    module, declaration, path, first, last = fields
    source = Path(path)
    assert source.is_file(), row
    start, stop = int(first), int(last)
    lines = source.read_text().splitlines()
    assert 1 <= start <= stop <= len(lines), row
    passage = "\n".join(lines[start - 1 : stop])
    assert "theorem " in passage and declaration.rsplit(".", 1)[-1] in passage, row
    listed.append(f"{module} {declaration}")
assert listed == Path(sys.argv[2]).read_text().splitlines()
PY
then
  echo "ok:   locations cover the same findings and name existing source lines"
else
  echo "FAIL: locations do not match the findings"
  cat "$WORK/list" "$WORK/err"
  FAIL=1
fi

expect_finding() {
  local label=$1 expected=$2 got
  check --baseline "$WORK/case" >"$WORK/out"
  got=$?
  if [ "$got" -eq 1 ] && grep -qxF "$expected" "$WORK/out"; then
    echo "ok:   $label fails with its finding"
  else
    echo "FAIL: $label returned $got without its finding"
    cat "$WORK/out" "$WORK/err"
    FAIL=1
  fi
}

grep -v '^CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused$' \
  "$WORK/expected" >"$WORK/case"
expect_finding "a theorem missing from the baseline" \
  "new: CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused"

{
  cat "$WORK/expected"
  echo "CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct_bound"
} >"$WORK/case"
expect_finding "a retained theorem in the baseline" \
  "stale baseline entry, no longer found: CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct_bound"

expect_error() {
  local label=$1 status=$2 got
  shift 2
  lake exe check-theorems "$@" >"$WORK/out" 2>"$WORK/err"
  got=$?
  if [ "$got" -eq "$status" ] && grep -q '^check-theorems:' "$WORK/err"; then
    echo "ok:   $label fails with exit $status"
  else
    echo "FAIL: $label returned $got, expected $status with a diagnostic"
    cat "$WORK/out" "$WORK/err"
    FAIL=1
  fi
}

printf '%s\n' 'only_one_column' >"$WORK/malformed"
expect_error "a malformed baseline" 2 --root scripts/CheckTheoremsTest \
  --baseline "$WORK/malformed"

printf '%s\n' 'CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused extra' >"$WORK/malformed"
expect_error "extra baseline columns" 2 --root scripts/CheckTheoremsTest \
  --baseline "$WORK/malformed"

{
  cat "$WORK/expected"
  echo "CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused"
} >"$WORK/duplicate"
expect_error "a duplicate baseline entry" 2 --root scripts/CheckTheoremsTest \
  --baseline "$WORK/duplicate"

expect_error "a missing baseline file" 2 --root scripts/CheckTheoremsTest \
  --baseline "$WORK/missing"

expect_error "an unknown option" 2 --unknown
expect_error "an option without its argument" 2 --root
expect_error "conflicting output modes" 2 --print --list
expect_error "an unnamed root" 2 --root scripts/CheckTheoremsTest/

mkdir "$WORK/Empty"
expect_error "a root with no specification declarations" 3 --root "$WORK/Empty" \
  --baseline "$WORK/expected"

exit "$FAIL"
