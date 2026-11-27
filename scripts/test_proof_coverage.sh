#!/usr/bin/env bash
# The coverage report must grade exactly the pairs that scripts/ProofCoverageTest plants.
# Its check must fail on a dropped pair and on an unrecorded new one, and each wrong claim
# and each malformed input must fail.
# Run from anywhere.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if ! lake build --wfail ProofCoverageTest proof-coverage >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures or the report do not build"; cat "$WORK/build"; exit 1
fi

coverage() {
  lake exe proof-coverage --src scripts --scope ProofCoverageTest \
    --claims "$WORK/claims" --baseline "$WORK/baseline" "$@" 2>"$WORK/err"
}

echo "ProofCoverageTest.sync ProofCoverageTest.sync_bounded  # Altair to Shapella" >"$WORK/claims"

# The doc comment of each fixture says why it has these lines.
cat >"$WORK/expected" <<'END'
# Written by `lake exe proof-coverage --update`; CONTRIBUTING.md says when to update it.
# Each line is a tier, a beacon fork and a consensus rule, for each pair above executable.
touched phase0 ProofCoverageTest.early
touched phase0 ProofCoverageTest.eligible
touched altair ProofCoverageTest.eligible
touched bellatrix ProofCoverageTest.eligible
touched shapella ProofCoverageTest.eligible
touched dencun ProofCoverageTest.eligible
touched pectra ProofCoverageTest.eligible
touched fusaka ProofCoverageTest.eligible
touched glamsterdam ProofCoverageTest.eligible
touched hegota ProofCoverageTest.eligible
touched glamsterdam ProofCoverageTest.payload
characterized altair ProofCoverageTest.sync
characterized bellatrix ProofCoverageTest.sync
characterized shapella ProofCoverageTest.sync
touched dencun ProofCoverageTest.sync
touched pectra ProofCoverageTest.sync
touched fusaka ProofCoverageTest.sync
touched glamsterdam ProofCoverageTest.sync
touched hegota ProofCoverageTest.sync
END

if coverage --update >"$WORK/out" && diff -u "$WORK/expected" "$WORK/baseline"; then
  echo "ok:   every planted pair is graded, and nothing else"
else
  echo "FAIL: the grades differ from the planted ones"; cat "$WORK/out" "$WORK/err"; FAIL=1
fi

# The counts at each fork, and the rule and the theorem whose fork hypothesis is unread.
coverage >"$WORK/report"
for line in \
  "proof-coverage: 5 rules, 5 property theorems" \
  "phase0: 2 rules, 2 touched, 0 characterized" \
  "altair: 2 rules, 2 touched, 1 characterized" \
  "fusaka: 3 rules, 2 touched, 0 characterized" \
  "glamsterdam: 4 rules, 3 touched, 0 characterized" \
  "unread fork hypotheses, at no fork: ProofCoverageTest.odd" \
  "unread fork hypotheses, at no fork: ProofCoverageTest.sync_odd"; do
  if grep -qxF -- "$line" "$WORK/report"; then
    echo "ok:   the report prints: $line"
  else
    echo "FAIL: the report does not print: $line"; cat "$WORK/report" "$WORK/err"; FAIL=1
  fi
done

cp "$WORK/expected" "$WORK/baseline"
if coverage --check >"$WORK/out"; then
  echo "ok:   the baseline that the code computes passes"
else
  echo "FAIL: the baseline that the code computes does not pass"; cat "$WORK/out" "$WORK/err"
  FAIL=1
fi

# Each case edits the exact baseline once, and names the line that the check must print.
# A difference exits with 1, and any other code is a crash, not a detection.
expect_fail() {
  local what=$1 line=$2 got
  coverage --check >"$WORK/out"; got=$?
  if [ "$got" -eq 1 ] && grep -qxF -- "$line" "$WORK/out"; then
    echo "ok:   $what fails the check"
  else
    echo "FAIL: $what is not reported with exit 1 (exit $got)"; cat "$WORK/out" "$WORK/err"
    FAIL=1
  fi
}

{ cat "$WORK/expected"; echo "touched hegota ProofCoverageTest.payload"; } >"$WORK/baseline"
expect_fail "a pair that drops a tier" "- touched hegota ProofCoverageTest.payload"

grep -vxF "touched glamsterdam ProofCoverageTest.payload" "$WORK/expected" >"$WORK/baseline"
expect_fail "an unrecorded new pair" "+ touched glamsterdam ProofCoverageTest.payload"

sed 's/^characterized altair /touched altair /' "$WORK/expected" >"$WORK/baseline"
expect_fail "an unrecorded rise of a tier" "+ characterized altair ProofCoverageTest.sync"

# Each wrong claim fails, with the reason, even without --check.
cp "$WORK/expected" "$WORK/baseline"
expect_claim() {
  local what=$1 claim=$2 message=$3 got
  echo "$claim" >"$WORK/claims"
  coverage >"$WORK/out"; got=$?
  if [ "$got" -eq 1 ] && grep -qxF -- "proof-coverage: wrong claim: $message" "$WORK/err"; then
    echo "ok:   $what fails"
  else
    echo "FAIL: $what is not reported with exit 1 (exit $got)"; cat "$WORK/out" "$WORK/err"
    FAIL=1
  fi
}

expect_claim "a claim on a definition that is no rule" \
  "ProofCoverageTest.Pair.left ProofCoverageTest.sync_eq" \
  "ProofCoverageTest.Pair.left is not a rule of ProofCoverageTest"
expect_claim "a claim on a rule whose window is unread" \
  "ProofCoverageTest.odd ProofCoverageTest.sync_eq" \
  "ProofCoverageTest.odd is not a rule of ProofCoverageTest"
expect_claim "a claim by a theorem that does not mention the rule" \
  "ProofCoverageTest.payload ProofCoverageTest.sync_eq" \
  "the statement of ProofCoverageTest.sync_eq does not mention ProofCoverageTest.payload"
expect_claim "a claim by a theorem of a specification module" \
  "ProofCoverageTest.eligible ProofCoverageTest.eligible_zero" \
  "ProofCoverageTest.eligible_zero is not a theorem of a property module with a readable fork window"
expect_claim "a claim by a theorem whose window is unread" \
  "ProofCoverageTest.sync ProofCoverageTest.sync_odd" \
  "ProofCoverageTest.sync_odd is not a theorem of a property module with a readable fork window"

# Malformed input exits with 2.
expect_malformed() {
  local what=$1 message=$2 got
  shift 2
  coverage "$@" >"$WORK/out"; got=$?
  if [ "$got" -eq 2 ] && grep -qF -- "$message" "$WORK/err"; then
    echo "ok:   $what exits with 2"
  else
    echo "FAIL: exit $got on $what, expected 2"; cat "$WORK/out" "$WORK/err"; FAIL=1
  fi
}

echo "ProofCoverageTest.sync" >"$WORK/claims"
expect_malformed "a claim without a theorem" "claims:1: expected a rule and a theorem"
printf 'ProofCoverageTest.sync ProofCoverageTest.sync_eq\n' >"$WORK/claims"
printf 'ProofCoverageTest.sync ProofCoverageTest.sync_eq\n' >>"$WORK/claims"
expect_malformed "a repeated claim" "claims:2: duplicate claim"
: >"$WORK/claims"
echo "proved altair ProofCoverageTest.sync" >"$WORK/baseline"
expect_malformed "an unknown tier" "baseline:1: expected a tier, a fork and a rule" --check
echo "touched berlin ProofCoverageTest.sync" >"$WORK/baseline"
expect_malformed "a fork that is no beacon fork" "baseline:1: berlin is not a beacon fork" --check
expect_malformed "an unknown argument" "unknown or incomplete argument --chek" --chek
expect_malformed "both modes" "choose either --check or --update" --check --update

exit "$FAIL"
