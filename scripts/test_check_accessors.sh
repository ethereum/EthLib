#!/usr/bin/env bash
# The accessor check must report exactly the sites planted in
# scripts/CheckAccessorsTest, pass once a baseline lists them, and fail on a
# new site, a stale entry, a wrong count, a scan that loads no definition and a
# root with no last part.
# Run from anywhere.
set -uo pipefail
cd "$(dirname "$0")/.."
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if ! lake build --wfail CheckAccessorsTest check-accessors >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures or the check do not build"; cat "$WORK/build"; exit 1
fi

check() { lake exe check-accessors --root scripts/CheckAccessorsTest "$@" 2>"$WORK/err"; }

# One line per planted site, in the format of the baseline.
# The doc comment of each fixture says why it has this entry, or none.
cat >"$WORK/expected" <<'END'
GetElem?.getElem! CheckAccessorsTest.Hidden.opaqueBody 1
GetElem?.getElem! CheckAccessorsTest.Spec.at0 1
ByteArray.get! CheckAccessorsTest.Spec.bump 1
ByteArray.set! CheckAccessorsTest.Spec.bump 1
GetElem?.getElem! CheckAccessorsTest.Spec.cond 1
GetElem?.getElem! CheckAccessorsTest.Spec.first 1
GetElem?.getElem! CheckAccessorsTest.Spec.first_eq 1
GetElem?.getElem! CheckAccessorsTest.Spec.first_of_zero 1
GetElem?.getElem! CheckAccessorsTest.Spec.hidden 1
ByteArray.get! CheckAccessorsTest.Spec.isOne 1
Array.back! CheckAccessorsTest.Spec.last 1
panicWithPosWithDecl CheckAccessorsTest.Spec.nonzero 1
GetElem?.getElem! CheckAccessorsTest.Spec.sumFirsts 1
GetElem?.getElem! CheckAccessorsTest.Spec.twice 2
GetElem?.getElem! CheckAccessorsTest.Spec.withLet 1
END

if check --print >"$WORK/found" && diff -u "$WORK/expected" "$WORK/found"; then
  echo "ok:   every planted site is reported, and nothing else"
else
  echo "FAIL: the sites differ from the planted ones"; cat "$WORK/err"; FAIL=1
fi

if check --baseline "$WORK/expected" >"$WORK/out"; then
  echo "ok:   a baseline that lists every site passes"
else
  echo "FAIL: a baseline that lists every site does not pass"; cat "$WORK/out"; FAIL=1
fi

# Each case edits the exact baseline once, and names the line that the check must print.
# A mismatch exits with 1; any other code is a crash, not a detection.
expect_fail() {
  local what=$1 line=$2 got
  check --baseline "$WORK/case" >"$WORK/out"; got=$?
  if [ "$got" -eq 1 ] && grep -qxF "$line" "$WORK/out"; then
    echo "ok:   $what fails the check"
  else
    echo "FAIL: $what is not reported with exit 1 (exit $got)"; cat "$WORK/out" "$WORK/err"; FAIL=1
  fi
}

grep -v ' CheckAccessorsTest.Spec.last ' "$WORK/expected" >"$WORK/case"
expect_fail "a site missing from the baseline" "new: Array.back! CheckAccessorsTest.Spec.last 1"

{ cat "$WORK/expected"; echo "GetElem?.getElem! CheckAccessorsTest.Spec.safe 1"; } >"$WORK/case"
expect_fail "a stale entry" \
  "stale baseline entry, no longer found: GetElem?.getElem! CheckAccessorsTest.Spec.safe 1"

sed 's/ CheckAccessorsTest.Spec.twice 2$/ CheckAccessorsTest.Spec.twice 3/' \
  "$WORK/expected" >"$WORK/case"
expect_fail "an entry above its count" \
  "fewer than listed, lower the entry: GetElem?.getElem! CheckAccessorsTest.Spec.twice 2, listed 3"

sed 's/ CheckAccessorsTest.Spec.twice 2$/ CheckAccessorsTest.Spec.twice 1/' \
  "$WORK/expected" >"$WORK/case"
expect_fail "an entry below its count" \
  "more than listed: GetElem?.getElem! CheckAccessorsTest.Spec.twice 2, listed 1"

# The proof tree holds no module of the specification, so the scan loads no definition.
lake exe check-accessors --root scripts/CheckAccessorsTest/Proofs --baseline "$WORK/expected" \
  >"$WORK/out" 2>"$WORK/err"; got=$?
empty="check-accessors: no definition of the specification was loaded"
if [ "$got" -eq 3 ] && grep -qxF "$empty" "$WORK/err"; then
  echo "ok:   a scan that loads no definition fails the check"
else
  echo "FAIL: exit $got on an empty scan, expected 3"; cat "$WORK/out" "$WORK/err"; FAIL=1
fi

# A root that ends in a separator has no last part to name its modules.
lake exe check-accessors --root scripts/CheckAccessorsTest/ --baseline "$WORK/expected" \
  >"$WORK/out" 2>"$WORK/err"; got=$?
noroot="check-accessors: the root scripts/CheckAccessorsTest/ has no last part to name its modules"
if [ "$got" -eq 2 ] && grep -qxF "$noroot" "$WORK/err"; then
  echo "ok:   a root with no last part is rejected"
else
  echo "FAIL: exit $got on a root with no last part, expected 2"
  cat "$WORK/out" "$WORK/err"; FAIL=1
fi

exit "$FAIL"
