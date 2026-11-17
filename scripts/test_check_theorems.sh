#!/usr/bin/env bash
# The theorem check must distinguish specification dependencies from unneeded properties.
# Its baseline must list exactly the findings, and malformed input must fail.
set -uo pipefail
cd "$(dirname "$0")/.."
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if ! lake build --wfail CheckTheoremsTest CheckTheoremsAttributesTest check-theorems \
    >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures or the check do not build"
  cat "$WORK/build"
  exit 1
fi

if python3 - "$WORK" <<'PY'
import json
from pathlib import Path
import subprocess
import sys

from scripts.check_theorems_baseline import BaselineError, entries

cases = json.loads(Path("scripts/check_theorems_baseline_cases.json").read_text())
path = Path(sys.argv[1]) / "parser-case"
binary = Path(".lake/build/bin/check-theorems").resolve()
for case in cases:
    path.write_text(case["text"], encoding="utf-8")
    result = subprocess.run(
        [str(binary), "--parse-baseline", str(path)], capture_output=True, text=True, check=False
    )
    if "error" in case:
        expected = f"{path}:{case['error']}"
        try:
            entries(case["text"], str(path))
        except BaselineError as error:
            assert str(error) == expected, case["name"]
        else:
            raise AssertionError(f"Python accepted {case['name']}")
        assert result.returncode == 2, (case["name"], result)
        assert result.stdout == "", (case["name"], result)
        assert result.stderr == f"check-theorems: {expected}\n", (case["name"], result)
    else:
        expected = "".join(f"{module} {decl}\n" for module, decl in case["entries"])
        assert entries(case["text"], str(path)) == {tuple(row) for row in case["entries"]}
        assert result.returncode == 0, (case["name"], result)
        assert result.stdout == expected, (case["name"], result)
        assert result.stderr == "", (case["name"], result)
PY
then
  echo "ok:   Lean and Python parse the shared baseline cases identically"
else
  echo "FAIL: the baseline parsers disagree with the shared cases"
  FAIL=1
fi

# Damaged reference metadata must fail before the checker reports movable theorems.
if python3 - "$WORK" <<'PY'
import json
import os
from pathlib import Path
import subprocess
import sys

work = Path(sys.argv[1]).resolve()
root = work / "Metadata"
root.mkdir()
source = root.with_suffix(".lean")
source.write_text("def metadataRoot : Nat := 0\n", encoding="utf-8")
compiled = work / "compiled"
compiled.mkdir()
olean = compiled / "Metadata.olean"
ilean = compiled / "Metadata.ilean"
subprocess.run(
    ["lake", "env", "lean", "-R", str(work), "-o", str(olean), "-i", str(ilean), str(source)],
    check=True,
)
env = os.environ.copy()
search_path = subprocess.run(
    ["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, check=True
).stdout.strip()
env["LEAN_PATH"] = str(compiled) + os.pathsep + search_path
binary = Path(".lake/build/bin/check-theorems").resolve()
original = ilean.read_text(encoding="utf-8")
metadata = json.loads(original)
cases = [
    ("valid", original, 0, ""),
    ("missing", None, 2, f"{ilean}: cannot read reference metadata"),
    ("corrupt", "{", 2, f"{ilean}: cannot read reference metadata"),
    (
        "wrong module",
        json.dumps({**metadata, "module": "Different"}),
        2,
        f"{ilean}: unexpected reference metadata module or version",
    ),
    (
        "wrong version",
        json.dumps({**metadata, "version": metadata["version"] + 1}),
        2,
        f"{ilean}: unexpected reference metadata module or version",
    ),
]
for label, content, status, diagnostic in cases:
    if content is None:
        ilean.unlink()
    else:
        ilean.write_text(content, encoding="utf-8")
    result = subprocess.run(
        [str(binary), "--root", str(root), "--print"],
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == status, (label, result)
    assert result.stdout == "", (label, result)
    expected_error = f"check-theorems: {diagnostic}\n" if diagnostic else ""
    assert result.stderr == expected_error, (label, result)
PY
then
  echo "ok:   missing, corrupt and mismatched reference metadata fail with their diagnostics"
else
  echo "FAIL: damaged reference metadata does not fail with its diagnostic"
  FAIL=1
fi

check() {
  lake env .lake/build/bin/check-theorems --root scripts/CheckTheoremsTest "$@" 2>"$WORK/err"
}

# Names and defining modules are hand-written, independent of the checker output.
LC_ALL=C sort >"$WORK/expected" <<'END'
CheckTheoremsTest root_unused
CheckTheoremsTest.Hidden CheckTheoremsTest.Spec.private_unused
CheckTheoremsTest.PrivateDependency CheckTheoremsTest.PrivateDependency.imported_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.deprecated_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct._proof_99
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.erased_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.erased_unused_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.inherited_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.local_eq
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.orphan._proof_1
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.orphan.eq_1
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.private_local_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.private_unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.private_with_local_definition
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.proof_local_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.sumTo_succ
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused_helper
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.used_only_from_exports
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.used_only_from_proofs
CheckTheoremsTest.Spec CheckTheoremsTest.Spec.with_local_definition
CheckTheoremsTest.Spec UnrelatedNamespace.unused
END

if check --print >"$WORK/found" && [ ! -s "$WORK/err" ] &&
    diff -u "$WORK/expected" "$WORK/found"; then
  echo "ok:   every unneeded theorem is reported, and nothing else"
else
  echo "FAIL: findings differ from the planted theorems"
  cat "$WORK/err"
  FAIL=1
fi

printf '%s\n' 'check-theorems: 5 modules, 22 findings, 0 new, 0 stale' >"$WORK/report"
if check --baseline "$WORK/expected" >"$WORK/out" && [ ! -s "$WORK/err" ] &&
    diff -u "$WORK/report" "$WORK/out"; then
  echo "ok:   an exact baseline passes"
else
  echo "FAIL: an exact baseline fails"
  cat "$WORK/out" "$WORK/err"
  FAIL=1
fi

# Source locations support migration without making line numbers part of the baseline.
if check --list >"$WORK/list" && [ ! -s "$WORK/err" ] &&
    python3 - "$WORK/list" "$WORK/expected" <<'PY'
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
  local label=$1 expected=$2 fresh=$3 stale=$4 got
  check --baseline "$WORK/case" >"$WORK/out"
  got=$?
  {
    printf '%s\n' "$expected"
    printf 'check-theorems: 5 modules, 22 findings, %s new, %s stale\n' "$fresh" "$stale"
  } >"$WORK/report"
  if [ "$got" -eq 1 ] && [ ! -s "$WORK/err" ] &&
      diff -u "$WORK/report" "$WORK/out"; then
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
  "new: CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused" 1 0

{
  cat "$WORK/expected"
  echo "CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct_bound"
} >"$WORK/case"
expect_finding "a retained theorem in the baseline" \
  "stale baseline entry, no longer found: CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct_bound" \
  0 1

grep -v '^CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused$' \
  "$WORK/case" >"$WORK/both"
mv "$WORK/both" "$WORK/case"
expect_finding "simultaneous new and stale findings" \
  "$(printf '%s\n' \
    'new: CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused' \
    'stale baseline entry, no longer found: CheckTheoremsTest.Spec CheckTheoremsTest.Spec.direct_bound')" \
  1 1

expect_error() {
  local label=$1 status=$2 message=$3 got
  shift 3
  lake env .lake/build/bin/check-theorems "$@" >"$WORK/out" 2>"$WORK/err"
  got=$?
  printf 'check-theorems: %s\n' "$message" >"$WORK/expected-err"
  if [ "$got" -eq "$status" ] && [ ! -s "$WORK/out" ] && \
      diff -u "$WORK/expected-err" "$WORK/err"; then
    echo "ok:   $label fails with exit $status and its diagnostic"
  else
    echo "FAIL: $label returned $got, expected $status with its diagnostic"
    cat "$WORK/out" "$WORK/err"
    FAIL=1
  fi
}

printf '%s\n' 'only_one_column' >"$WORK/malformed"
expect_error "a malformed baseline" 2 \
  "$WORK/malformed:1: expected a module and a declaration name" \
  --root scripts/CheckTheoremsTest \
  --baseline "$WORK/malformed"

printf '%s\n' 'CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused extra' >"$WORK/malformed"
expect_error "extra baseline columns" 2 \
  "$WORK/malformed:1: expected a module and a declaration name" \
  --root scripts/CheckTheoremsTest \
  --baseline "$WORK/malformed"

{
  cat "$WORK/expected"
  echo "CheckTheoremsTest.Spec CheckTheoremsTest.Spec.unused"
} >"$WORK/duplicate"
duplicate_line=$(($(wc -l <"$WORK/expected") + 1))
expect_error "a duplicate baseline entry" 2 \
  "$WORK/duplicate:$duplicate_line: duplicate baseline entry" \
  --root scripts/CheckTheoremsTest \
  --baseline "$WORK/duplicate"

expect_error "a missing baseline file" 2 "$WORK/missing: cannot read baseline" \
  --root scripts/CheckTheoremsTest \
  --baseline "$WORK/missing"

expect_error "an unknown option" 2 "unknown or incomplete option --unknown" --unknown
expect_error "an option without its argument" 2 "unknown or incomplete option --root" --root
expect_error "a root option followed by another option" 2 "--root needs a directory" \
  --root --print
expect_error "a baseline option followed by another option" 2 "--baseline needs a file" \
  --baseline --print
expect_error "a parse option without its argument" 2 \
  "unknown or incomplete option --parse-baseline" --parse-baseline
expect_error "a parse option followed by another option" 2 "--parse-baseline needs a file" \
  --parse-baseline --print
expect_error "conflicting parse and output modes" 2 \
  "choose either --parse-baseline or other options" --parse-baseline "$WORK/expected" --list
expect_error "conflicting output modes" 2 "choose either --print or --list" --print --list
expect_error "an unnamed root" 2 "the root has no last part to name its modules" \
  --root scripts/CheckTheoremsTest/

mkdir "$WORK/Empty"
expect_error "a root with no specification declarations" 3 \
  "no definition of the specification was loaded" --root "$WORK/Empty" \
  --baseline "$WORK/expected"

attribute_diagnostics=$(cat <<'END'
scripts/CheckTheoremsAttributesTest/Spec.lean:18: unsupported persistent attribute [csimp] on theorem CheckTheoremsAttributesTest.compiler_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:21: unsupported persistent attribute [placement_simp] on theorem CheckTheoremsAttributesTest.custom_simp_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:29: unsupported persistent attribute [grind] on theorem CheckTheoremsAttributesTest.grind_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:37: unsupported persistent attribute [ext] on theorem CheckTheoremsAttributesTest.ext_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:44: unsupported persistent attribute [elab_as_elim] on theorem CheckTheoremsAttributesTest.eliminator_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:44: unsupported persistent attribute [induction_eliminator] on theorem CheckTheoremsAttributesTest.eliminator_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:44: unsupported persistent attribute [cases_eliminator] on theorem CheckTheoremsAttributesTest.eliminator_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:51: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.tagged_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:54: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.private_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:57: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.scoped_declaration_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:63: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.mixed_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:68: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.command_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:73: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.scoped_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:103: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.localSyntax_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:123: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.localCommand_rule
scripts/CheckTheoremsAttributesTest/Spec.lean:126: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.identity
scripts/CheckTheoremsAttributesTest/Spec.lean:129: unsupported persistent attribute [placement_tag] on theorem CheckTheoremsAttributesTest.metadata_mixed_rule
END
)
expect_error "unsupported persistent attributes" 2 "$attribute_diagnostics" \
  --root scripts/CheckTheoremsAttributesTest --print

exit "$FAIL"
