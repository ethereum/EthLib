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
  -- The release version, the same as in `pyproject.toml` (`scripts/release_manifest.py`).
  version := v!"0.2.0"
  moreLeancArgs := #["-fPIC"]

require "leanprover-community" / "mathlib" @ git "v4.35.0"

-- Probability and oracle computations, for the leanXMSS and BLS security proofs only.
--
-- The library code never imports it.
--
-- A commit on VCVio's `main`, built against the same Mathlib.
require VCVio from git "https://github.com/Verified-zkEVM/VCVio.git" @
  "bbf05eeeedf84c5f98baaf5ab846f2d2479cc8ab"

@[default_target]
lean_lib «EthLib» where
  -- Lean v4.35.0, Source Files and Modules, section 5.4.
  -- Ordinary importers load public definitions without private proof bodies.
  requiresModuleSystem := true
  precompileModules := true

/-- Proofs about the specification.

The executable specification never depends on this library.

Theorems produce no code, so `precompileModules` is off.

Proof object files then stay out of the Python extension link.

`platformIndependent` keeps the specification's shared library out of each proof's trace.

A proof then rebuilds only when a module it imports changes.

Each domain's proof tree is a root, so its modules belong here and not to `EthLib`. -/
@[default_target]
lean_lib «Proofs» where
  requiresModuleSystem := true
  roots := #[`EthLib.Proofs, `EthLib.Serialization.Proofs, `EthLib.Cryptography.Proofs, `EthLib.Networking.Proofs,
    `EthLib.Execution.Proofs, `EthLib.Consensus.Proofs, `EthLib.Base.Proofs]
  precompileModules := false
  platformIndependent := true

/-- The C exports the Python extension calls, and nothing else. A separate
library (rooted at `EthLib/Exports.lean`), so that the specification never
imports an `@[export]` symbol or the `IO` that turns a typed error into a
Python exception. `precompileModules` is on: these objects are the ones
`setup.py` links.

Each domain's export tree is also a root, so that its modules belong to
this library rather than to `EthLib`. -/
@[default_target]
lean_lib «Exports» where
  requiresModuleSystem := true
  roots := #[`EthLib.Exports, `EthLib.Cryptography.Exports, `EthLib.Networking.Exports,
    `EthLib.Execution.Exports, `EthLib.Consensus.Exports, `EthLib.Serialization.Exports]
  precompileModules := true

/-- Checks the compiled declarations of every library: their axioms, and any
construct the kernel cannot unfold or the compiler runs differently. Run it
after `lake build` with `lake exe check-decls`. -/
lean_exe «check-decls» where
  srcDir := "scripts"
  root := `CheckDecls
  supportInterpreter := true
  -- The checker loads private proof bodies to inspect their dependencies.
  allowNonModules := true

/-- Declarations the check must catch, and one module it must pass. Not a
default target: `scripts/test_check_decls.sh` builds and checks it. -/
lean_lib «CheckDeclsTest» where
  srcDir := "scripts"
  roots := #[`CheckDeclsTest, `CheckDeclsForeign]
  -- The classic root checks findings behind ordinary module boundaries.
  allowNonModules := true
