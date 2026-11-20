import Lake
open Lake DSL System

/-!
Lake build for `EthLib`.

The package is pure Lean, with no external C dependencies.

Lake produces:

* per-Lean-module `.c.o.export` object files in `.lake/build/ir/`,
* per-module `.olean` files in `.lake/build/lib/lean/`.

`setup.py` builds the Python C extension under `bindings/python/`, not Lake.

It selects `.c.o.export` files through the ordinary imports of `EthLib.Exports`.

It links these objects into one Python extension beside the shared Lean runtime.
-/

package «EthLib» where
  -- The release version, the same as in `pyproject.toml` (`scripts/release_manifest.py`).
  version := v!"0.3.0"
  moreLeancArgs := #["-fPIC", "-ffunction-sections", "-fdata-sections"]

require "leanprover-community" / "mathlib" @ git "v4.36.0"

-- Probability and oracle computations, for the security proofs.
--
-- `SOUNDNESS.md` (D2) lists the proofs that import it, directly or through another file.
--
-- `scripts/soundness_facts.py` generates that list.
--
-- The library code never imports it.
--
-- The paired cache theorem preserves full hash replies in the leanXMSS proof.
require VCVio from git "https://github.com/Verified-zkEVM/VCVio.git" @ "6f8b75511932ed54e901c3d978b3022a66961f8d"

@[default_target]
lean_lib «EthLib» where
  -- Lean v4.36.0, Source Files and Modules, section 5.4.
  --
  -- Ordinary importers load public definitions without private proof bodies.
  requiresModuleSystem := true
  precompileModules := true

/-- Proofs about the specification.

The executable specification never depends on this library.

`precompileModules` is off, since default targets need no native proof objects.

The Python extension links only the runtime imports of `EthLib.Exports`.

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
  -- Mathlib's concrete-instances linter flags an instance assumption without variables.
  --
  -- It asks for a global instance in its place, or for its removal when one exists.
  --
  -- The SPHINCS+ proofs quantify over every parameter class, and a global instance fixes one.
  --
  -- The random-oracle bounds hold for every sampler of digests, and a removal keeps one.
  --
  -- So either fix narrows a statement.
  leanOptions := #[⟨`weak.linter.concreteInstances, false⟩]

/-- The C exports the Python extension calls, and nothing else.

It is a separate library, so that the specification never imports an `@[export]` symbol.

`precompileModules` builds the objects that `setup.py` links.

One root and its initializer name make this a plugin, so the specification's plugin loads first.

The extension initializes only runtime imports.

The linker discards EthLib's unused compile-time and legacy initializers.

The globs assign each domain's export tree to this library. -/
@[default_target]
lean_lib «Exports» where
  requiresModuleSystem := true
  roots := #[`EthLib.Exports]
  libName := "EthLib_EthLib_Exports"
  -- The conversion core and its laws belong to `PythonConversions` below.
  globs := #[.one `EthLib.Exports, .one `EthLib.Base.Exports,
    .one `EthLib.Base.Exports.Bindings, .one `EthLib.Base.Exports.ChainConfig,
    .one `EthLib.Base.Exports.Echo, .one `EthLib.Base.Exports.Fin,
    .one `EthLib.Base.Exports.PyDerive, .one `EthLib.Base.Exports.PyValue,
    .one `EthLib.Base.Exports.PyValueJson,
    .andSubmodules `EthLib.Cryptography.Exports, .andSubmodules `EthLib.Networking.Exports,
    .andSubmodules `EthLib.Execution.Exports, .andSubmodules `EthLib.Consensus.Exports,
    .andSubmodules `EthLib.Serialization.Exports, .andSubmodules `EthLib.Engine.Exports]
  precompileModules := true
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticExportFacet]

/-- Python conversion types and the proofs of their laws.

The core imports only the Lean toolchain, and the law module imports only the core.

These modules belong to neither `Exports` nor `Proofs`.

Lake assigns a module to the last library whose globs match it, so this block stays after `Proofs`.

A downstream project can then precompile the exports without a native library cycle.

The bindings link the core's runtime objects, but not the meta-imported law module. -/
lean_lib «PythonConversions» where
  requiresModuleSystem := true
  roots := #[`EthLib.Base.Exports.Result, `EthLib.Base.Exports.PyValueCore,
    `EthLib.Base.Proofs.Exports.PyValue]
  libName := "EthLib_PythonConversions"
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
