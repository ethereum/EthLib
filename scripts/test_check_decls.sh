#!/usr/bin/env bash
# The declaration check must report exactly the findings planted in
# scripts/CheckDeclsTest, pass once a baseline lists them, and fail on a
# baseline entry that no longer matches. Run from anywhere.
set -uo pipefail
cd "$(dirname "$0")/.."
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# The fixtures contain `sorry` on purpose, so they are built without --wfail.
if ! lake build CheckDeclsTest >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures do not build"; cat "$WORK/build"; exit 1
fi

check() { lake exe check-decls --scope CheckDeclsTest "$@" CheckDeclsTest; }

# One line per planted finding: its kind, then the declaration it is reported at.
# `usesNative` and everything in Good and Exports must not appear.
# CheckDeclsForeign is outside the scope, as a dependency would be.
LC_ALL=C sort >"$WORK/expected" <<'EOF'
axiom CheckDeclsTest.Bad.Phantom._native
axiom CheckDeclsTest.Bad.assumed
axioms CheckDeclsTest.Bad.Carrier
axioms CheckDeclsTest.Bad.usesAssumed
csimp CheckDeclsTest.Bad.double_eq_doubleFast
extern CheckDeclsTest.Bad.external
implemented_by CheckDeclsTest.Bad.slow
native CheckDeclsTest.Bad.native
native CheckDeclsTest.Proofs.Native.big
opaque CheckDeclsTest.Bad.hidden
partial CheckDeclsTest.Bad.spin
reaches-opaque CheckDeclsTest.Bad.countdown
reaches-opaque CheckDeclsTest.Bad.fallback
reaches-opaque CheckDeclsTest.Bad.fallbackMessage
sorry CheckDeclsTest.Bad.unfinished
unsafe CheckDeclsTest.Bad.Ghost._unsafe_rec
unsafe CheckDeclsTest.Bad.reinterpret
EOF

check --baseline /dev/null >"$WORK/out"; got=$?
grep -vE '^(check-decls:|stale )' "$WORK/out" | cut -d: -f1 | LC_ALL=C sort -u >"$WORK/found"
if [ "$got" -ne 1 ]; then
  echo "FAIL: exit $got with an empty baseline, expected 1"; FAIL=1
fi
if diff -u "$WORK/expected" "$WORK/found"; then
  echo "ok:   every planted finding is reported, and nothing else"
else
  echo "FAIL: the findings differ from the planted ones"; FAIL=1
fi

if check --baseline "$WORK/expected" >"$WORK/out"; then
  echo "ok:   a baseline that lists every finding passes"
else
  echo "FAIL: a baseline that lists every finding does not pass"; cat "$WORK/out"; FAIL=1
fi

{ cat "$WORK/expected"; echo "partial CheckDeclsTest.Good.double"; } >"$WORK/stale"
if ! check --baseline "$WORK/stale" >"$WORK/out" \
   && grep -qx 'stale baseline entry, no longer found: partial CheckDeclsTest.Good.double' "$WORK/out"; then
  echo "ok:   a stale baseline entry is reported, and fails the check"
else
  echo "FAIL: a stale baseline entry is not handled"; cat "$WORK/out"; FAIL=1
fi

exit "$FAIL"
