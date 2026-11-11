import Lake
open Lake DSL System

/-!
Lake build for `EthLib`.

The package is pure Lean, with no external C dependencies.

Lake produces:

* per-Lean-module `.c.o.export` object files in `.lake/build/ir/`,
* per-module `.olean` files in `.lake/build/lib/lean/`.

`setup.py` builds the Python C extension under `bindings/python/`, not Lake.

It enumerates the `.c.o.export` files and the Lean toolchain's static archives.

It links them all statically into a single self-contained Python extension.
-/

package «EthLib» where
  -- The release version, the same as in `pyproject.toml` (`scripts/release_manifest.py`).
  version := v!"0.3.0"
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
    `EthLib.Execution.Proofs, `EthLib.Consensus.Proofs, `EthLib.Base.Proofs, `EthLib.Engine.Proofs]
  precompileModules := false
  platformIndependent := true

/-- The C exports the Python extension calls, and nothing else.

It is a separate library, so that the specification never imports an `@[export]` symbol.

`precompileModules` is on, because `setup.py` links these objects.

Each domain's export tree is also a root, so that its modules belong to this library. -/
@[default_target]
lean_lib «Exports» where
  requiresModuleSystem := true
  roots := #[`EthLib.Exports, `EthLib.Base.Exports, `EthLib.Cryptography.Exports,
    `EthLib.Networking.Exports, `EthLib.Execution.Exports, `EthLib.Consensus.Exports,
    `EthLib.Serialization.Exports, `EthLib.Engine.Exports]
  precompileModules := true

/-- Checks the compiled declarations of every library.

It checks their axioms, and any construct the kernel cannot unfold or the compiler runs differently.

Run it after `lake build` with `lake exe check-decls`. -/
lean_exe «check-decls» where
  srcDir := "scripts"
  root := `CheckDecls
  supportInterpreter := true
  -- The checker loads private proof bodies to inspect their dependencies.
  allowNonModules := true

/-- Writes the binding contract from the Lean docstrings and error codes.

Run it after `lake build Exports` with `lake exe gen-bindings`.

With `--check`, it fails when a generated file is stale. -/
lean_exe «gen-bindings» where
  srcDir := "scripts"
  root := `GenBindings
  supportInterpreter := true

/-- Declarations the check must catch, and one module it must pass.

Not a default target: `scripts/test_check_decls.sh` builds and checks it. -/
lean_lib «CheckDeclsTest» where
  srcDir := "scripts"
  roots := #[`CheckDeclsTest, `CheckDeclsForeign]
  -- The classic root checks findings behind ordinary module boundaries.
  allowNonModules := true

/-- Lists the defaulting accessors of the specification, such as `xs[i]!`, `set!` and `get!`.

It compares them with an exact list that may only shrink.

Run it after `lake build` with `lake exe check-accessors`. -/
lean_exe «check-accessors» where
  srcDir := "scripts"
  root := `CheckAccessors
  supportInterpreter := true
  allowNonModules := true
