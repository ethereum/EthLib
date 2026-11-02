# Building EthLib

Two commands build everything.
`lake exe cache get` fetches Mathlib's published artifacts, so that Mathlib is not compiled from source.
`lake build --wfail` then compiles EthLib and checks every proof, with warnings treated as errors.

## Module boundaries

EthLib uses the module system of Lean v4.35.0.
A module decides which of its declarations other files can see, and how much of each one they see.
That matters for two reasons.
Clients need the definitions of the specification, and sometimes their bodies, to state and prove things about them.
A proof, on the other hand, is nobody else's business, so when only a proof changes, the files that import it should not have to rebuild.
The language rules are in [Source Files and Modules, sections 5.4 and 5.6.1](https://lean-lang.org/doc/reference/4.35.0/Source-Files-and-Modules/).

A definition file has this shape:

```lean
module

public import EthLib.Cryptography.Hash.Sha256

/-! A module docstring. -/

@[expose] public section

-- Definitions and theorems.
```

Each part of that shape has a reason.
A public import keeps the names that clients receive through the library roots.
An exposed definition keeps its body visible, so the reductions that client proofs rely on still work.
The proof of a theorem stays private, even inside an exposed section.
A file that only imports other files needs no section.
The helper definitions of an exposed implementation must be public as well, since the exposed body refers to them.
C exports use a plain `public section`, because clients execute them through the bindings.

Proofs sometimes need more than the public interface offers.
A proof-only import can use a plain `import` when it contributes nothing to the public API.
When you reason about a dependency, prefer its public equations.
If a proof needs the body of a definition, a targeted `import all` can provide it, either from the same package or from a dependency that permits private imports.
Comment the exact definition whose body the proof needs.
Give a public definition an explicit result type when a delayed proof cannot infer it.
Keep compatibility options such as `backward.proofsInPublic` disabled.

The library, the proofs and the C exports remain three separate Lake libraries.
The declaration checker loads modules at Lean's `.private` level, so that it can inspect proof bodies and private helpers.
Its fixtures include module files, and a classic root that loads their private information.

After you change these boundaries, run the module regression:

```bash
bash scripts/test_module_system.sh
```

It checks ordinary imports.
It also checks that changing a private proof leaves the public artifact unchanged, so that a downstream build is skipped.
Public metadata still changes when source positions move, so a proof edit does not always avoid downstream builds.

## CI cache and timing

A full build of EthLib is slow, so CI caches it.
CI restores only EthLib's `.lake/build`, and only from successful pushes to `master`, while Mathlib uses its own published cache.
The EthLib cache key includes the operating system, the architecture, the toolchain and the dependency manifest.
Pull requests read the cache but never publish one, and the manual workflow's `clean_build` input skips the restore.

Before saving, CI deletes the generated `*.setup.json` files from the build directory.
These files contain absolute runner paths, and Lake regenerates them.
The cache uses version `v2`, so that it cannot restore entries saved before this cleanup.

Native objects are platform-specific.
The build therefore does not claim the platform independence that CompPoly's library-only release archive relies on.

The job summary reports the wall time and the CPU work of each build and test stage.
The exports are measured before the bindings are installed, to keep their timing separate from the uv package build.
The `ethlib-build-timing` artifact holds the logs, the timing records, the module tables and the report.

Per-module comparisons use the last samples stored with the restored build.
They compare the same rebuilt modules, and keep the precision Lake reports.
Native compilation counts in the command timings, but not in the elaboration table.
A small difference can come from parallel load or from noise on the runner.

The build pipeline regressions change one export in an isolated Lean project, and check that its timing reaches the report.
They also inspect a saved tar archive, restore it, and check that Lake needs no rebuild.
Run them after installing the test dependencies:

```bash
uv run --no-project --python 3.12 python -m unittest discover -s scripts -p 'test_build_pipeline.py'
```

To time a local command:

```bash
export BUILD_TIMING_LOG_DIR=/tmp/ethlib-timing
bash scripts/build_timing_report.sh run library_build "$BUILD_TIMING_LOG_DIR/results.jsonl" -- lake build --wfail EthLib
bash scripts/build_timing_report.sh render "$BUILD_TIMING_LOG_DIR/results.jsonl"
```

The setup follows [ArkLib's migration](https://github.com/Verified-zkEVM/ArkLib/blob/bc367f8d53f603a48c5502e1ad7d39b7b3be725c/docs/wiki/module-system.md) and [VCVio's boundary policy](https://github.com/Verified-zkEVM/VCVio/blob/aae1c9cbd6c00311091d691b74f2d0032d76d9bd/docs/agents/module-system.md).
[CompPoly's cache guide](https://github.com/Verified-zkEVM/CompPoly/blob/9be21b026e43ff9b032113dc9b766d2b17fd6c3c/docs/wiki/build-cache.md) distinguishes dependency caches from release archives.
The sources and license of the ported timing scripts are recorded in [BUILD_TIMING_SOURCES.md](scripts/BUILD_TIMING_SOURCES.md).
