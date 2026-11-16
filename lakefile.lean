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

-- Probability and oracle computations, for the security proofs.
--
-- `SOUNDNESS.md` (D2) lists the proofs that import it, directly or through another file.
--
-- `scripts/soundness_facts.py` generates that list.
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

One root and its initializer name make this a plugin, so the specification's plugin loads first.

Lake sorts plugins by dependency, but Lean loads ordinary dynamic libraries before them.

The globs assign each domain's export tree to this library. -/
@[default_target]
lean_lib «Exports» where
  requiresModuleSystem := true
  -- Lean v4.35.0, Lake/Config/LeanLib.lean, `LeanLib.isPlugin`.
  roots := #[`EthLib.Exports]
  libName := "EthLib_EthLib_Exports"
  -- Lake/Build/Module.lean, `computeModuleDeps`; Lean/Elab/Frontend.lean, `runFrontend`.
  globs := #[.one `EthLib.Exports, .andSubmodules `EthLib.Base.Exports,
    .andSubmodules `EthLib.Cryptography.Exports, .andSubmodules `EthLib.Networking.Exports,
    .andSubmodules `EthLib.Execution.Exports, .andSubmodules `EthLib.Consensus.Exports,
    .andSubmodules `EthLib.Serialization.Exports, .andSubmodules `EthLib.Engine.Exports]
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

/-- Runs pinned test vectors through the compiled specification, with no export in between.

No default target builds it.

`lake exe known-answers` builds and runs it. -/
lean_exe «known-answers» where
  srcDir := "scripts"
  root := `KnownAnswers

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
  -- The checker loads private definition bodies to find the accessors they call.
  allowNonModules := true

/-- Sites the accessor check must count, and sites it must skip.

Not a default target: `scripts/test_check_accessors.sh` builds and checks it. -/
lean_lib «CheckAccessorsTest» where
  srcDir := "scripts"
  roots := #[`CheckAccessorsTest]

/-- Source attribute inspection used by the theorem placement check. -/
lean_lib «CheckTheoremSupport» where
  srcDir := "scripts"
  roots := #[`CheckTheoremAttributes]
  allowNonModules := true

/-- Checks that specification theorems support definitions, instances or simplification.

It compares the remaining theorems with an exact baseline that may only shrink.

Run it after `lake build` with `lake exe check-theorems`. -/
lean_exe «check-theorems» where
  srcDir := "scripts"
  root := `CheckTheorems
  supportInterpreter := true
  -- The dependency search loads private definition and proof bodies.
  allowNonModules := true

/-- Theorems the placement check must keep, report or skip.

Not a default target: `scripts/test_check_theorems.sh` builds and checks it. -/
lean_lib «CheckTheoremsTest» where
  srcDir := "scripts"
  roots := #[`CheckTheoremsTest]

/-- Persistent theorem attributes on which the placement check must stop.

Not a default target: `scripts/test_check_theorems.sh` builds and checks it. -/
lean_lib «CheckTheoremsAttributesTest» where
  srcDir := "scripts"
  roots := #[`CheckTheoremsAttributesTest]
  allowNonModules := true
