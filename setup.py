"""Build the `ethlib.cryptography._native` CPython extension from the Lean exports."""

import json
import platform
import subprocess
from pathlib import Path

from setuptools import Extension, find_packages, setup
from setuptools.command.build_ext import build_ext

REPO_ROOT = Path(__file__).parent.resolve()
BINDINGS = REPO_ROOT / "bindings" / "python"
LAKE_IR = REPO_ROOT / ".lake" / "build" / "ir"


def _lean_sysroot() -> Path | None:
    """
    The prefix of the active Lean toolchain, or `None` when no `lean` is on PATH.

    The sdist build only archives source files, so Lean is needed only to compile the extension.
    """
    try:
        out = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None
    return Path(out)


def _collect_lean_objects() -> list[str]:
    """
    The objects in the runtime import graph of `EthLib.Exports`.

    Lean's `.ilean` records distinguish ordinary imports from `meta import`.

    The latter supply compile-time code or erased proofs, so their objects do not enter the link.

    Follow ordinary imports regardless of their path, and require every object on that walk.

    Unreachable objects left by a proof build or by a moved module then cannot enter the link.
    """
    objects = []
    pending = ["EthLib.Exports"]
    visited = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        module_path = Path(*module.split("."))
        source = REPO_ROOT / module_path.with_suffix(".lean")
        if not source.is_file():
            raise RuntimeError(f"runtime Lean source is missing: {source}")
        ilean = LAKE_IR.parent / "lib" / "lean" / module_path.with_suffix(".ilean")
        metadata = json.loads(ilean.read_text())
        if metadata.get("version") != 5 or metadata.get("module") != module:
            raise RuntimeError(f"unsupported or mismatched Lean import metadata: {ilean}")
        obj = LAKE_IR / module_path.with_suffix(".c.o.export")
        if not obj.is_file():
            raise RuntimeError(f"runtime Lean object is missing: {obj}")
        objects.append(str(obj))
        # Lean v4.36.0, Lean/Data/Lsp/Internal.lean, `ImportInfo.toJson`.
        for imported, _private, _all, meta in metadata["directImports"]:
            if not meta and (imported == "EthLib" or imported.startswith("EthLib.")):
                pending.append(imported)
    return sorted(objects)


def _native_link_args(build_temp: Path) -> list[str]:
    """
    Discard unused EthLib compile-time and legacy initializers, keeping other native exports.

    A module's object holds runtime, compile-time and legacy initializers.

    Python calls only runtime initializers; the other phases can refer to proof modules.

    Hiding those two initializer families lets the linker discard their unused sections.
    """
    if platform.system() == "Darwin":
        return [
            "-Wl,-dead_strip",
            "-Wl,-unexported_symbol,_meta_initialize_EthLib_*",
            "-Wl,-unexported_symbol,_initialize_EthLib_*",
        ]
    build_temp.mkdir(parents=True, exist_ok=True)
    exports = build_temp / "native-exports.map"
    exports.write_text("{ global: *; local: meta_initialize_EthLib_*; initialize_EthLib_*; };\n")
    # Bind references to the extension's own definitions before discarding unused sections.
    return ["-Wl,-Bsymbolic", "-Wl,--gc-sections", f"-Wl,--version-script={exports.resolve()}"]


def _lean_runtime_link(sysroot: Path) -> tuple[list[str], list[str], list[str]]:
    """
    The extra objects, library directories and libraries that link the Lean runtime.

    The extension links `libleanshared` dynamically, on every platform.

    The static archives of Lean are not `-fPIC` on Linux, so they cannot go in a shared object.

    `auditwheel` and `delocate` bundle the shared runtime into each wheel and patch its RPATH.

    So an installed wheel needs no Lean toolchain.

    `libgmp.a` and `libuv.a`, when the toolchain has them, stay static inputs.
    """
    gmp_uv = [
        str(p) for p in (sysroot / "lib" / "libgmp.a", sysroot / "lib" / "libuv.a") if p.exists()
    ]
    return gmp_uv, [str(sysroot / "lib" / "lean")], ["leanshared"]


class LakeThenBuild(build_ext):
    """
    Build the Lean exports with Lake, then the extension with setuptools.

    Conversion proofs are checked while the exports elaborate, but only runtime objects link.
    """

    def run(self):
        """Build the Lean exports, then link their objects into each extension."""
        # Build the exports, their specification imports and their conversion proofs.
        subprocess.check_call(["lake", "build", "Exports"], cwd=str(REPO_ROOT))
        sysroot = _lean_sysroot()
        if sysroot is None:
            raise RuntimeError(
                "lean toolchain not found on PATH; install elan before building the C extension"
            )
        # Re-resolve include_dirs and link inputs lazily.
        # At metadata time (e.g. `uv build --sdist`) Lean may not be installed.
        runtime_objs, library_dirs, libraries = _lean_runtime_link(sysroot)
        native_link_args = _native_link_args(Path(self.build_temp))
        for ext in self.extensions:
            if str(sysroot / "include") not in ext.include_dirs:
                ext.include_dirs.append(str(sysroot / "include"))
            ext.extra_objects = _collect_lean_objects() + runtime_objs
            ext.extra_link_args = list(ext.extra_link_args or []) + native_link_args
            for d in library_dirs:
                if d not in ext.library_dirs:
                    ext.library_dirs.append(d)
                # Also add to runtime_library_dirs.
                # This lets local dev (without auditwheel) find libleanshared at runtime via RPATH.
                if d not in ext.runtime_library_dirs:
                    ext.runtime_library_dirs.append(d)
            for lib in libraries:
                if lib not in ext.libraries:
                    ext.libraries.append(lib)
        super().run()


def _make_extension() -> Extension:
    extra_link_args: list[str] = []
    libraries: list[str] = []

    if platform.system() == "Darwin":
        # libleancpp is C++ — drag in libc++.
        libraries.append("c++")
    else:
        libraries.append("stdc++")
        # On Linux, Lean's symbols use thread-local storage and pthreads.
        libraries.append("pthread")
        libraries.append("dl")
        libraries.append("m")

    # `LakeThenBuild.run` appends the Lean-toolchain include dir and the `.c.o.export` objects.
    # They are not resolved here.
    # This lets metadata-only invocations (sdist) work without elan installed.
    return Extension(
        name="ethlib.cryptography._native",
        sources=[
            "bindings/python/module.c",
            "bindings/python/engine.c",
            "bindings/python/kzg.c",
            "bindings/python/bls.c",
            "bindings/python/xmss.c",
            "bindings/python/sphincs.c",
            "bindings/python/sha256.c",
            "bindings/python/keccak.c",
            "bindings/python/ethash.c",
            "bindings/python/vrf.c",
            "bindings/python/crc32.c",
            "bindings/python/crc32c.c",
            "bindings/python/aes.c",
            "bindings/python/hmac.c",
            "bindings/python/password_kdf.c",
            "bindings/python/x25519.c",
            "bindings/python/chacha20_poly1305.c",
            "bindings/python/noise.c",
            "bindings/python/deposit_tree.c",
            "bindings/python/keystore.c",
            "bindings/python/secp256k1.c",
            "bindings/python/secp256r1.c",
            "bindings/python/precompile.c",
            "bindings/python/enr.c",
            "bindings/python/state.c",
            "bindings/python/trie.c",
            "bindings/python/consensus.c",
            "bindings/python/reqresp.c",
            "bindings/python/blocks.c",
            "bindings/python/evm.c",
            "bindings/python/fees.c",
            "bindings/python/pow.c",
            "bindings/python/discv5.c",
            "bindings/python/rlp.c",
            "bindings/python/ssz.c",
            "bindings/python/rlpx.c",
            "bindings/python/devp2p.c",
            "bindings/python/discv4.c",
            "bindings/python/forkid.c",
            "bindings/python/eth.c",
            "bindings/python/snap.c",
            "bindings/python/era1.c",
            "bindings/python/era.c",
            "bindings/python/snappy.c",
            "bindings/python/libp2p.c",
            "bindings/python/quic.c",
            "bindings/python/gossip.c",
            "bindings/python/transactions.c",
            "bindings/python/chain.c",
            "bindings/python/rpc.c",
            "bindings/python/pyvalue.c",
        ],
        include_dirs=["bindings/python"],
        extra_objects=[],
        libraries=libraries,
        extra_link_args=extra_link_args,
    )


setup(
    package_dir={"": "bindings/python"},
    # Each directory under the package root that has an `__init__.py`, so no list can drift.
    packages=find_packages(where="bindings/python", include=["ethlib", "ethlib.*"]),
    # The type stub of the extension, which `lake exe gen-bindings` writes from Lean.
    package_data={"ethlib": ["py.typed"], "ethlib.cryptography": ["_native.pyi"]},
    ext_modules=[_make_extension()],
    cmdclass={"build_ext": LakeThenBuild},
)
