# Build timing sources

`module_times.py` and `build_timing_report.sh` are adapted from ArkLib and VCVio.
These two scripts retain the upstream Apache-2.0 license.
The license text is in [Apache-2.0.txt](Apache-2.0.txt).

The source revisions are:

- [ArkLib bc367f8](https://github.com/Verified-zkEVM/ArkLib/tree/bc367f8d53f603a48c5502e1ad7d39b7b3be725c/scripts).
- [VCVio aae1c9c](https://github.com/Verified-zkEVM/VCVio/tree/aae1c9cbd6c00311091d691b74f2d0032d76d9bd/scripts).

EthLib records separate commands for the specification, exports, bindings, vector suites, proofs, and declaration check.
The module table includes only EthLib elaboration times.
It excludes dependencies, checker fixtures, and native compilation facets.

The table follows the restored build cache.
Each rebuilt module replaces its last recorded time.
Deleted source files leave the table.
The sum is recorded compile work under parallel load, not a prediction of clean-build elapsed time.
