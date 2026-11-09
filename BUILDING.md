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
CI restores EthLib's `.lake/build` only from successful pushes to `master`, while Mathlib uses its own published cache.
The EthLib cache key includes the operating system, the architecture, the toolchain and the dependency manifest.
Pull requests read the cache but never publish one.

The library and the exports import no module of Mathlib, VCVio or their dependencies.
So the jobs that need only the library and the exports do not fetch the Mathlib cache: the `suites` job and the workflows `bench` and `vectors-slow`.
They run `lake env true`, which clones the packages that Lake needs to load the workspace.

A new push to a pull request cancels the run still in progress on that pull request.
On `master`, the run in progress finishes, and the latest push waits until it ends.
GitHub keeps one waiting run for each group, so a newer push replaces the older waiting run.

The Mathlib cache does not hold the builds of VCVio, PolyFun and cslib, which the proofs import.
So CI caches their `.lake/build` directories separately, under a key of the operating system, the architecture, the toolchain and the dependency manifest.
Each successful push to `master` saves this cache under a new key, and a run restores the newest entry for its toolchain and manifest.
So a module of these packages that EthLib starts to import is cached after the next push to `master`.
Lake compares content hashes, so it rebuilds a restored module whose inputs differ.

The manual workflow's `clean_build` input skips both restores, so the run builds EthLib and these packages from scratch.

The cache saves the most time when a change rebuilds only the proofs that it affects.
Because `EthLib` sets `precompileModules`, Lake loads the native shared library of all of `EthLib` into each proof that imports the specification.
By default, Lake also adds that shared library to the trace of the proof, so a change to any specification module rebuilds every proof.
The `Proofs` library sets `platformIndependent`, which keeps platform-dependent inputs such as this shared library out of the traces of its modules.
A proof then does not rebuild for a change to a specification module that it does not import.
It still rebuilds when the `.olean` files of a module that it imports change.

Before saving, CI deletes the generated `*.setup.json` files from the build directory.
These files contain absolute runner paths, and Lake regenerates them.
The cache uses version `v2`, so that it cannot restore entries saved before this cleanup.

Native objects are platform-specific.
The build therefore does not claim the platform independence that CompPoly's library-only release archive relies on.

The vector suites need only the library, so they run in the `suites` job, beside the proofs in the `build` job.
Each job builds the library and the exports from the restored cache, and only the `build` job saves a cache.

The job summary reports the wall time and the CPU work of each build and test stage.
The exports are measured before the bindings are installed, to keep their timing separate from the uv package build.
The `ethlib-build-timing` artifact holds the logs, the timing records, the module tables and the report of the `build` job.
The `ethlib-suites-timing` artifact holds the logs and the report of the `suites` job.

Per-module comparisons use the last samples stored with the restored build.
They compare the same rebuilt modules, and keep the precision Lake reports.
Native compilation counts in the command timings, but not in the elaboration table.
A small difference can come from parallel load or from noise on the runner.

The build pipeline regressions build an isolated Lean project with the default libraries of `lakefile.lean` and their settings.
They change one export, and check that its timing reaches the report.
They change a specification module that the proof of the project does not import, and check that the proof does not rebuild.
Then they change the module that the proof imports, and check that the proof rebuilds.
They also inspect a saved tar archive, restore it, and check that Lake needs no rebuild of any default target.
Run them after installing the test dependencies:

```bash
uv run --no-sync python -m unittest discover -s scripts -p 'test_build_pipeline.py'
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

## Memory

CI builds EthLib on a GitHub runner with 16 GB of memory, and Lake elaborates several files at once.
A file that needs too much memory can therefore stop the whole build.
So on a pull request, CI elaborates each Lean file that the pull request adds or changes once more, after the proofs.
The job summary gives the time and the peak memory of each of these files.
A file that needs more than 4 GiB gets a warning, and a file that needs more than 6 GiB fails the job.

A clean build runs as many Lean processes at once as `LEAN_NUM_THREADS` allows, so their memory adds up.
On master `b001695`, a clean `lake build --wfail` peaked at 8.1 GiB of Lean processes with 4 at once, and at 9.2 GiB with 8.
No file needed more than 3.8 GiB, and the largest is the order certificate of secp256k1.
Known answers stay out of Lean, since one of them can need several GiB, and their vectors run in the Python suite, as [CONTRIBUTING.md](CONTRIBUTING.md#known-answers) asks.
To build with fewer processes, set the thread count with the CPU affinity, as in `LEAN_NUM_THREADS=4 taskset -c 0-3 lake build --wfail`, because Lake ignores `taskset` when it sizes its pool.

To measure files on your machine, build their imports first, then run:

```bash
uv run --no-project --python 3.12 python scripts/check_memory.py <file>...
```
