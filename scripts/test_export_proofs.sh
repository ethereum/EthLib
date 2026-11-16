#!/usr/bin/env bash
# An isolated package checks native loading when a property imports a C export.
# Copy the production library settings, including roots, globs and native library names.
# An optional lakefile argument checks another configuration without editing this tree.
set -euo pipefail
cd "$(dirname "$0")/.."
export_proofs_dir=$(mktemp -d)
export_proofs_lakefile=${1:-lakefile.lean}
cleanup() {
  local result=$?
  if [ "$result" -ne 0 ]; then
    for log in "$export_proofs_dir"/*.log; do
      if [ -f "$log" ]; then cat "$log"; fi
    done
  fi
  rm -rf "$export_proofs_dir"
}
trap cleanup EXIT

python3 - "$export_proofs_dir" "$export_proofs_lakefile" <<'PY'
from pathlib import Path
import re
import shutil
import sys

project = Path(sys.argv[1])
source = Path(sys.argv[2]).read_text()
pattern = re.compile(
    r"^@\[default_target\]\nlean_lib «(\w+)» where\n(?:[ \t]+.*\n)*",
    re.MULTILINE,
)
libraries = {match.group(1): match.group(0) for match in pattern.finditer(source)}
assert set(libraries) == {"EthLib", "Proofs", "Exports"}, libraries
shutil.copyfile("lean-toolchain", project / "lean-toolchain")
(project / "lakefile.lean").write_text(
    "import Lake\nopen Lake DSL System\n"
    'package «EthLib» where\n  moreLeancArgs := #["-fPIC"]\n\n'
    + "\n".join(libraries.values())
)


def write(module, text):
    path = project / (module.replace(".", "/") + ".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


# Empty domain roots preserve the real ownership graph without external dependencies.
roots = {"EthLib"}
for stanza in libraries.values():
    roots.update(re.findall(r"`(EthLib(?:\.\w+)*)", stanza))
for module in roots:
    write(module, "module\n")

domains = ["Base", "Cryptography", "Networking", "Execution", "Consensus", "Serialization", "Engine"]
write("EthLib", "module\npublic import EthLib.Base.Value\n")
write(
    "EthLib.Base.Value",
    "module\n@[expose] public section\n"
    "namespace EthLib.Base\n"
    "structure Config where\n  bytes : ByteArray\n  lengths : List Nat\n"
    "def configuration : Config := ⟨⟨#[11, 23, 41, 97]⟩, [3, 5, 7]⟩\n"
    "end EthLib.Base\n",
)
for domain in domains:
    write(
        f"EthLib.{domain}.Exports",
        f"module\npublic import EthLib.{domain}.Exports.Probe\n",
    )
    write(
        f"EthLib.{domain}.Exports.Probe",
        "module\npublic import EthLib.Base.Value\n@[expose] public section\n"
        f"namespace EthLib.{domain}.Exports\n"
        f'@[export ethlib_export_proofs_{domain.lower()}]\n'
        "def probe (bytes : ByteArray) : ByteArray :=\n"
        "  EthLib.Base.configuration.bytes ++ bytes\n"
        f"end EthLib.{domain}.Exports\n",
    )
write(
    "EthLib.Exports",
    "module\n" + "".join(f"public import EthLib.{domain}.Exports\n" for domain in domains),
)
write(
    "EthLib.Base.Proofs.Hex",
    "module\npublic import EthLib.Base.Value\n@[expose] public section\n"
    "namespace EthLib.Base\n"
    "theorem append_empty (bytes : ByteArray) : bytes ++ ByteArray.empty = bytes := by simp\n"
    "end EthLib.Base\n",
)
write("EthLib.Base.Proofs", "module\npublic import EthLib.Base.Proofs.Hex\n")
write(
    "EthLib.Serialization.Proofs.Exports",
    "module\npublic import EthLib.Base.Proofs.Hex\n"
    "public import EthLib.Serialization.Exports.Probe\n@[expose] public section\n"
    "namespace EthLib.Serialization\n"
    "theorem probe_append_empty (bytes : ByteArray) :\n"
    "    Exports.probe bytes ++ ByteArray.empty = EthLib.Base.configuration.bytes ++ bytes := by\n"
    "  rw [EthLib.Base.append_empty]\n  rfl\n"
    "end EthLib.Serialization\n",
)
write(
    "EthLib.Serialization.Proofs",
    "module\npublic import EthLib.Serialization.Proofs.Exports\n",
)
write(
    "EthLib.Proofs",
    "module\n" + "".join(f"public import EthLib.{domain}.Proofs\n" for domain in domains),
)
PY

check_objects() {
  python3 - "$export_proofs_dir" <<'PY'
import ast
from glob import glob
from pathlib import Path
import sys

project = Path(sys.argv[1])
tree = ast.parse(Path("setup.py").read_text())
functions = [
    node for node in tree.body
    if isinstance(node, ast.FunctionDef)
    and node.name in {"_current_objects", "_collect_lean_objects"}
]
assert len(functions) == 2
namespace = {
    "glob": glob,
    "Path": Path,
    "REPO_ROOT": project,
    "LAKE_IR": project / ".lake/build/ir",
}
exec(compile(ast.Module(body=functions, type_ignores=[]), "setup.py", "exec"), namespace)
objects = [Path(path).relative_to(project) for path in namespace["_collect_lean_objects"]()]
assert any(path.name == "Value.c.o.export" for path in objects), objects
for domain in ["Base", "Cryptography", "Networking", "Execution", "Consensus", "Serialization", "Engine"]:
    expected = Path(f".lake/build/ir/EthLib/{domain}/Exports/Probe.c.o.export")
    assert expected in objects, (expected, objects)
# Strip the object suffix so an aggregate module named `Proofs` counts too.
for path in objects:
    parts = path.as_posix().removesuffix(".c.o.export").split("/")
    assert "Proofs" not in parts, path
native_proofs = [
    path for path in (project / ".lake/build/lib").rglob("*Proofs*")
    if path.is_file() and path.suffix in {".a", ".so", ".dylib", ".dll"}
]
assert not native_proofs, native_proofs
PY
}

(cd "$export_proofs_dir" && lake build --wfail Exports) >"$export_proofs_dir/exports.log" 2>&1
check_objects
if [ -e "$export_proofs_dir/.lake/build/lib/lean/EthLib/Base/Proofs/Hex.olean" ]; then
  echo "FAIL: building exports elaborated an ordinary property" >&2
  exit 1
fi

# A proof importing an export must load the specification's native plugin first.
(cd "$export_proofs_dir" && lake build --wfail) >"$export_proofs_dir/proofs.log" 2>&1
check_objects
test -f "$export_proofs_dir/.lake/build/lib/lean/EthLib/Serialization/Proofs/Exports.olean"
echo "ok:   properties import native exports with the production library settings"
echo "ok:   exports build without ordinary properties, and their objects exclude those properties"
