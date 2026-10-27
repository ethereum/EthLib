import Lake
open Lake DSL System

/-!
Lake build for `EthLib`.

The package is pure Lean — no external C dependencies. Lake produces:

* per-Lean-module `.c.o.export` object files in `.lake/build/ir/`,
* per-module `.olean` files in `.lake/build/lib/lean/`.

The Python C extension under `bindings/python/` is built by `setup.py`
(not Lake): it enumerates the `.c.o.export` files and the Lean
toolchain's static archives and statically links them all into a single
self-contained Python extension.
-/

package «EthLib» where
  moreLeancArgs := #["-fPIC"]

require "leanprover-community" / "mathlib" @ git "v4.29.1"

-- Pin the shared SSZ codec so the wire format has one implementation.
require ssz from git "https://github.com/ethereum/ssz-specs" @
  "a23a2392ffffdd72caefb12f57b7ebd0c9a49de5" / "lean"

@[default_target]
lean_lib «EthLib» where
  precompileModules := true

/-- Proofs about the specification. A separate library (rooted at
`EthLib/Proofs.lean`) so the executable spec never depends
on it. `precompileModules` is off: theorems produce no code, and this
keeps proof object files out of the Python extension link.

Each domain's proof tree is also a root, so that its modules belong to
this library rather than to `EthLib`. -/
@[default_target]
lean_lib «Proofs» where
  roots := #[`EthLib.Proofs, `EthLib.Cryptography.Proofs, `EthLib.Networking.Proofs]
  precompileModules := false

/-- The C exports the Python extension calls, and nothing else. A separate
library (rooted at `EthLib/Exports.lean`), so that the specification never
imports an `@[export]` symbol or the `IO` that turns a typed error into a
Python exception. `precompileModules` is on: these objects are the ones
`setup.py` links.

Each domain's export tree is also a root, so that its modules belong to
this library rather than to `EthLib`. -/
@[default_target]
lean_lib «Exports» where
  roots := #[`EthLib.Exports, `EthLib.Cryptography.Exports]
  precompileModules := true

/-- Checks the compiled declarations of every library: their axioms, and any
construct the kernel cannot unfold or the compiler runs differently. Run it
after `lake build` with `lake exe check-decls`. -/
lean_exe «check-decls» where
  srcDir := "scripts"
  root := `CheckDecls
  supportInterpreter := true

/-- Declarations the check must catch, and one module it must pass. Not a
default target: `scripts/test_check_decls.sh` builds and checks it. -/
lean_lib «CheckDeclsTest» where
  srcDir := "scripts"
  roots := #[`CheckDeclsTest, `CheckDeclsForeign]
