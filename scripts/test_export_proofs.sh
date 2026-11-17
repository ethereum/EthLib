#!/usr/bin/env bash
# An isolated package checks runtime linking when exports use erased conversion laws.
# Copy the production library settings, including their default native facets.
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
import ast
import re
import shutil
import sys

project = Path(sys.argv[1])
source = Path(sys.argv[2]).read_text()
pattern = re.compile(
    r"^(?:@\[default_target\]\n)?lean_lib «(\w+)» where\n(?:[ \t]+.*\n)*",
    re.MULTILINE,
)
names = {"EthLib", "Proofs", "Exports", "PythonConversions"}
libraries = {
    match.group(1): match.group(0)
    for match in pattern.finditer(source) if match.group(1) in names
}
assert set(libraries) == names, libraries
package = re.search(r"^package «EthLib» where\n(?:[ \t]+.*\n)*", source, re.MULTILINE)
assert package is not None
shutil.copyfile("lean-toolchain", project / "lean-toolchain")
(project / "lakefile.lean").write_text(
    "import Lake\nopen Lake DSL System\n"
    + package.group(0) + "\n"
    + "\n".join(libraries.values())
    + '\nlean_lib «Consumer» where\n  requiresModuleSystem := true\n'
    + '  roots := #[`Consumer]\n  precompileModules := true\n'
    + '\nlean_exe «compiled-consumer» where\n  root := `ConsumerMain\n'
)
helpers = [
    node for node in ast.parse(Path("setup.py").read_text()).body
    if isinstance(node, ast.FunctionDef)
    and node.name in {"_collect_lean_objects", "_native_link_args", "_lean_runtime_link"}
]
assert len(helpers) == 3
(project / "setup_helpers.py").write_text(ast.unparse(ast.Module(body=helpers, type_ignores=[])))


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
    probe = "Echo" if domain == "Base" else "Probe"
    write(
        f"EthLib.{domain}.Exports",
        f"module\npublic import EthLib.{domain}.Exports.{probe}\n",
    )
    write(
        f"EthLib.{domain}.Exports.{probe}",
        "module\npublic import EthLib.Base.Value\n"
        "public import EthLib.Base.Exports.PyValue\n@[expose] public section\n"
        f"namespace EthLib.{domain}.Exports\n"
        f'@[export ethlib_export_proofs_{domain.lower()}]\n'
        "def probe (bytes : ByteArray) : ByteArray :=\n"
        "  EthLib.Exports.pyExport (EthLib.Base.configuration.bytes ++ bytes)\n"
        f"end EthLib.{domain}.Exports\n",
    )
write(
    "EthLib.Base.Exports.Result",
    "module\npublic abbrev EthLib.Exports.Result (α : Type) := Except String α\n",
)
write(
    "EthLib.Base.Exports.PyValueCore",
    "module\npublic import EthLib.Base.Exports.Result\n"
    "@[expose] public section\nnamespace EthLib.Exports\n"
    "class PyCodec (α : Type) where\n"
    "  encode : α → ByteArray\n  decode : ByteArray → Option α\n"
    "instance : PyCodec ByteArray := ⟨id, some⟩\n"
    "class LawfulPy (α : Type) [PyCodec α] : Prop where\n"
    "  decode_encode (value : α) : PyCodec.decode (PyCodec.encode value) = some value\n"
    "def pyExport {α : Type} [PyCodec α] [LawfulPy α] (value : α) : ByteArray :=\n"
    "  PyCodec.encode value\nend EthLib.Exports\n",
)
write(
    "EthLib.Base.Proofs.Exports.PyValue",
    "module\npublic import EthLib.Base.Exports.PyValueCore\n@[expose] public section\n"
    "namespace EthLib.Exports\n"
    "def lawHelper : Option ByteArray → ByteArray\n"
    "  | some bytes => bytes\n  | none => ByteArray.empty\n"
    "instance : LawfulPy ByteArray where\n  decode_encode _ := rfl\n"
    "theorem lawHelper_some (bytes : ByteArray) : lawHelper (some bytes) = bytes := rfl\n"
    "end EthLib.Exports\n",
)
write(
    "EthLib.Base.Exports.PyValue",
    "module\npublic import EthLib.Base.Exports.PyValueCore\n"
    "public meta import EthLib.Base.Proofs.Exports.PyValue\n",
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
write(
    "EthLib.Base.Proofs",
    "module\npublic import EthLib.Base.Proofs.Hex\n"
    "public import EthLib.Base.Proofs.Exports.PyValue\n",
)
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
write(
    "Consumer",
    "module\npublic import EthLib.Exports\npublic import EthLib.Proofs\n"
    "@[expose] public section\n"
    "def consumer (bytes : ByteArray) : ByteArray := EthLib.Base.Exports.probe bytes\n"
    "theorem consumer_eq (bytes : ByteArray) :\n"
    "    consumer bytes = EthLib.Base.configuration.bytes ++ bytes := rfl\n",
)
write(
    "ConsumerMain",
    "module\nimport Consumer\n"
    "def main : IO Unit := do\n"
    "  let actual := consumer ⟨#[103]⟩\n"
    "  unless actual == (⟨#[11, 23, 41, 97, 103]⟩ : ByteArray) do\n"
    '    throw (IO.userError "compiled consumer returned the wrong bytes")\n',
)
PY

check_objects() {
  python3 - "$1" "$2" "$export_proofs_dir/setup_helpers.py" <<'PY'
import json
from pathlib import Path
import platform
import sys

project = Path(sys.argv[1])
real_library = sys.argv[2] == "real"
namespace = {
    "json": json,
    "platform": platform,
    "Path": Path,
    "REPO_ROOT": project,
    "LAKE_IR": project / ".lake/build/ir",
}

helpers = Path(sys.argv[3]).read_text()
exec(compile(helpers, "setup.py", "exec"), namespace)
objects = [Path(path).relative_to(project) for path in namespace["_collect_lean_objects"]()]
if real_library:
    # Every current export module must contribute its object, so exclusion cannot pass vacuously.
    expected = {
        Path(".lake/build/ir") / path.relative_to(project).with_suffix(".c.o.export")
        for path in (project / "EthLib").rglob("*.lean")
        if "Exports" in path.relative_to(project).with_suffix("").parts
        and "Proofs" not in path.relative_to(project).parts
    }
    anchors = {
        Path(".lake/build/ir/EthLib/Exports.c.o.export"),
        Path(".lake/build/ir/EthLib/Base/Exports/PyValue.c.o.export"),
        Path(".lake/build/ir/EthLib/Base/Exports/Echo.c.o.export"),
    }
    assert anchors <= expected, (anchors, expected)
    assert expected <= set(objects), sorted(expected - set(objects))
else:
    assert any(path.name == "Value.c.o.export" for path in objects), objects
    for domain in ["Base", "Cryptography", "Networking", "Execution", "Consensus", "Serialization", "Engine"]:
        probe = "Echo" if domain == "Base" else "Probe"
        expected = Path(f".lake/build/ir/EthLib/{domain}/Exports/{probe}.c.o.export")
        assert expected in objects, (expected, objects)
# Strip the object suffix so an aggregate module named `Proofs` counts too.
for path in objects:
    parts = path.as_posix().removesuffix(".c.o.export").split("/")
    assert "Proofs" not in parts, path
PY
}

link_fixture() {
  python3 - "$export_proofs_dir" <<'PY'
import ctypes
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys

project = Path(sys.argv[1])
namespace = {
    "json": json,
    "platform": platform,
    "Path": Path,
    "REPO_ROOT": project,
    "LAKE_IR": project / ".lake/build/ir",
}
exec(compile((project / "setup_helpers.py").read_text(), "setup.py", "exec"), namespace)
objects = namespace["_collect_lean_objects"]()
proof_object = project / ".lake/build/ir/EthLib/Base/Proofs/Exports/PyValue.c.o.export"
assert proof_object.is_file(), proof_object
assert str(proof_object) not in objects, objects
proof_symbols = subprocess.check_output(["nm", "-g", str(proof_object)], text=True)
assert "lawHelper" in proof_symbols, proof_symbols
sysroot = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
runtime_objects, library_dirs, libraries = namespace["_lean_runtime_link"](sysroot)
shim = project / "runtime.c"
shim.write_text(r"""
#include <lean/lean.h>
extern lean_object* runtime_initialize_EthLib_EthLib_Exports(uint8_t);
extern lean_object* ethlib_export_proofs_base(lean_object*);
LEAN_EXPORT int initialize_external_probe(void) { return 17; }
LEAN_EXPORT int meta_initialize_external_probe(void) { return 23; }
LEAN_EXPORT int PyInit__native(void) {
    lean_object* result = runtime_initialize_EthLib_EthLib_Exports(1);
    if (lean_io_result_is_error(result)) { lean_dec(result); return 0; }
    lean_dec(result);
    lean_object* input = lean_alloc_sarray(1, 1, 1);
    lean_sarray_cptr(input)[0] = 103;
    lean_object* output = ethlib_export_proofs_base(input);
    int valid = lean_sarray_size(output) == 5
        && lean_sarray_cptr(output)[0] == 11 && lean_sarray_cptr(output)[1] == 23
        && lean_sarray_cptr(output)[2] == 41 && lean_sarray_cptr(output)[3] == 97
        && lean_sarray_cptr(output)[4] == 103;
    lean_dec(output);
    return valid;
}
""")
library = project / ("runtime.dylib" if platform.system() == "Darwin" else "runtime.so")
command = shlex.split(os.environ.get("CC", "cc")) + [
    "-shared", "-fPIC", "-ffunction-sections", "-fdata-sections", "-DLEAN_EXPORTING",
    f"-I{sysroot / 'include'}", str(shim), *objects, *runtime_objects,
    *[f"-L{directory}" for directory in library_dirs],
    *[f"-Wl,-rpath,{directory}" for directory in library_dirs],
    *[f"-l{library}" for library in libraries],
    *namespace["_native_link_args"](project / "link"), "-o", str(library),
]
subprocess.run(command, check=True)
undefined = subprocess.check_output(["nm", "-u", str(library)], text=True)
assert "Proofs" not in undefined, undefined
symbol_args = ["-gU"] if platform.system() == "Darwin" else ["-D", "--defined-only"]
public_symbols = subprocess.check_output(["nm", *symbol_args, str(library)], text=True)
symbols = {line.split()[-1] for line in public_symbols.splitlines() if line.split()}
if platform.system() == "Darwin":
    symbols = {symbol.removeprefix("_") for symbol in symbols}
expected = {
    "PyInit__native", "runtime_initialize_EthLib_EthLib_Exports",
    "initialize_external_probe", "meta_initialize_external_probe",
} | {
    f"ethlib_export_proofs_{domain}"
    for domain in ["base", "cryptography", "networking", "execution", "consensus", "serialization", "engine"]
}
assert expected <= symbols, sorted(expected - symbols)
assert not any(
    symbol.startswith(("meta_initialize_EthLib_", "initialize_EthLib_")) for symbol in symbols
), symbols
native = ctypes.CDLL(str(library))
for symbol in expected:
    getattr(native, symbol)
native.PyInit__native.restype = ctypes.c_int
assert native.PyInit__native() == 1
assert native.initialize_external_probe() == 17
assert native.meta_initialize_external_probe() == 23
PY
}

(cd "$export_proofs_dir" && lake build --wfail Exports) >"$export_proofs_dir/exports.log" 2>&1
check_objects "$export_proofs_dir" fixture
if [ -e "$export_proofs_dir/.lake/build/lib/lean/EthLib/Base/Proofs/Hex.olean" ]; then
  echo "FAIL: building exports elaborated an ordinary property" >&2
  exit 1
fi

# A property can import exports, and a precompiled downstream consumer can import both.
(cd "$export_proofs_dir" && lake build --wfail) >"$export_proofs_dir/proofs.log" 2>&1
check_objects "$export_proofs_dir" fixture
test -f "$export_proofs_dir/.lake/build/lib/lean/EthLib/Serialization/Proofs/Exports.olean"
(cd "$export_proofs_dir" && lake build --wfail Exports:shared Consumer Consumer:shared) \
  >"$export_proofs_dir/consumer.log" 2>&1
(cd "$export_proofs_dir" && lake exe compiled-consumer) >"$export_proofs_dir/consumer-run.log" 2>&1
test -f "$export_proofs_dir/.lake/build/lib/lean/Consumer.olean"
check_objects "$export_proofs_dir" fixture

# Native plugins can contain laws; the extension's runtime walk must still exclude them.
(cd "$export_proofs_dir" && lake build --wfail EthLib.Base.Proofs.Exports.PyValue:c.o.export) \
  >"$export_proofs_dir/proof-native.log" 2>&1
check_objects "$export_proofs_dir" fixture
link_fixture >"$export_proofs_dir/runtime-link.log" 2>&1

# Ordinary imports remain runtime dependencies even when their module is under Proofs.
export_proofs_facade="$export_proofs_dir/EthLib/Base/Exports/PyValue.lean"
cp "$export_proofs_facade" "$export_proofs_dir/facade-meta.lean"
sed 's/public meta import/public import/' "$export_proofs_dir/facade-meta.lean" > "$export_proofs_facade"
(cd "$export_proofs_dir" && lake build --wfail Exports) >"$export_proofs_dir/ordinary.log" 2>&1
if check_objects "$export_proofs_dir" fixture >"$export_proofs_dir/ordinary-objects.log" 2>&1; then
  echo "FAIL: the no-property assertion accepted an ordinary import of conversion proofs" >&2
  exit 1
fi
if ! grep -Fq 'Base/Proofs/Exports/PyValue.c.o.export' "$export_proofs_dir/ordinary-objects.log"; then
  cat "$export_proofs_dir/ordinary-objects.log" >&2
  echo "FAIL: the ordinary-import regression failed for another reason" >&2
  exit 1
fi
cp "$export_proofs_dir/facade-meta.lean" "$export_proofs_facade"
(cd "$export_proofs_dir" && lake build --wfail Exports) >"$export_proofs_dir/restored.log" 2>&1
check_objects "$export_proofs_dir" fixture
echo "ok:   properties import exports with the production library settings"
echo "ok:   shared export libraries build, and a precompiled downstream consumer runs"
echo "ok:   erased laws elaborate, and a native extension preserves C exports without their object"
echo "ok:   the runtime walk excludes cached property objects and retains ordinary imports"

# Check the production graph too, including proof dependencies absent from the synthetic package.
lake build --wfail Exports Exports:shared >"$export_proofs_dir/real-exports.log" 2>&1
check_objects "$PWD" real
echo "ok:   every real export object is selected, and no real property object is selected"
