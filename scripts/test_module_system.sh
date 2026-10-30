#!/usr/bin/env bash
# Lean v4.35.0, Source Files and Modules, sections 5.4 and 5.6.1.
# Check ordinary consumers and proof-only invalidation without editing library sources.
set -euo pipefail
cd "$(dirname "$0")/.."
module_test_dir="$(mktemp -d)"
cleanup() {
  local result=$?
  if [ "$result" -ne 0 ]; then
    for log in "$module_test_dir"/*.log; do
      if [ -f "$log" ]; then cat "$log"; fi
    done
  fi
  rm -rf "$module_test_dir"
}
trap cleanup EXIT

# Include unimported source files, which the root modules would not otherwise check.
python3 - <<'PY'
from pathlib import Path
import re
from scripts.soundness_facts import strip_lean

paths = [Path("EthLib.lean"), *Path("EthLib").rglob("*.lean")]
classic = [str(path) for path in paths
           if not re.match(r"\s*module\b", strip_lean(path.read_text()))]
if classic:
    raise SystemExit("Missing module headers: " + ", ".join(classic))
PY

cat > "$module_test_dir/Consumer.lean" <<'EOF'
module
import EthLib
import EthLib.Proofs
import EthLib.Exports

example : EthLib.Networking.Encoding.Varint.groupSize = 128 := rfl

example : EthLib.Networking.Encoding.Varint.groupSize = 128 :=
  EthLib.Networking.Proofs.Encoding.Varint.groupSize_eq

#check EthLib.Cryptography.Bls.Exports.constBytesPerPubkey
EOF
lake env lean -DwarningAsError=true --root="$module_test_dir" "$module_test_dir/Consumer.lean"

# The same compiler checks the artifact boundary on a small, isolated import graph.
cp lean-toolchain "$module_test_dir/lean-toolchain"
cat > "$module_test_dir/lakefile.toml" <<'EOF'
name = "ModuleSystemTest"
defaultTargets = ["Consumer"]
[[lean_lib]]
name = "Consumer"
roots = ["Consumer", "Provider"]
requiresModuleSystem = true
EOF
cat > "$module_test_dir/Provider.lean" <<'EOF'
module
public theorem proofOnly : True := by exact True.intro
EOF
cat > "$module_test_dir/Consumer.lean" <<'EOF'
module
public import Provider
public theorem consumer : True := proofOnly
EOF
(cd "$module_test_dir" && lake build --wfail) > "$module_test_dir/first.log" 2>&1
cp "$module_test_dir/.lake/build/lib/lean/Provider.olean" "$module_test_dir/public-before.olean"
cp "$module_test_dir/.lake/build/lib/lean/Provider.olean.private" "$module_test_dir/private-before.olean"
cp "$module_test_dir/.lake/build/lib/lean/Consumer.trace" "$module_test_dir/consumer-before.trace"

# Keep the theorem's statement and source position; change only its private proof.
cat > "$module_test_dir/Provider.lean" <<'EOF'
module
public theorem proofOnly : True := by exact id True.intro
EOF
(cd "$module_test_dir" && lake build --wfail) > "$module_test_dir/second.log" 2>&1
cmp "$module_test_dir/public-before.olean" "$module_test_dir/.lake/build/lib/lean/Provider.olean"
cmp "$module_test_dir/consumer-before.trace" "$module_test_dir/.lake/build/lib/lean/Consumer.trace"
if cmp -s "$module_test_dir/private-before.olean" "$module_test_dir/.lake/build/lib/lean/Provider.olean.private"; then
  echo 'FAIL: the proof edit must change the private artifact' >&2
  exit 1
fi
if ! grep -Fq 'Built Provider' "$module_test_dir/second.log" \
    || grep -Fq 'Built Consumer' "$module_test_dir/second.log"; then
  cat "$module_test_dir/second.log"
  echo 'FAIL: a private proof edit must rebuild its provider and skip its consumer' >&2
  exit 1
fi
echo 'ok: ordinary imports expose specifications, theorems, and exports'
echo 'ok: a private proof edit preserves the public artifact and skips its consumer'
