# Build timing sources

`module_times.py` and `build_timing_report.sh` are adapted from ArkLib and VCVio.
These two scripts retain the upstream Apache-2.0 license, whose text is in [Apache-2.0.txt](Apache-2.0.txt).
They were adapted from these source revisions:

- [ArkLib bc367f8](https://github.com/Verified-zkEVM/ArkLib/tree/bc367f8d53f603a48c5502e1ad7d39b7b3be725c/scripts).
- [VCVio aae1c9c](https://github.com/Verified-zkEVM/VCVio/tree/aae1c9cbd6c00311091d691b74f2d0032d76d9bd/scripts).

EthLib records a separate command for each of the specification, the exports, the bindings, the vector suites, the proofs and the declaration check.
The module table, by contrast, lists only the time Lean spends elaborating EthLib's own modules.
It excludes dependencies, the checker fixtures and native compilation facets.

The table follows the restored build cache.
Each rebuilt module replaces its last recorded time, and a deleted source file leaves the table.
The sum of the table is therefore the compile work recorded under parallel load, not a prediction of how long a clean build takes.
