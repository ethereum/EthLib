# Consensus test vectors

A preset or a configuration of the beacon chain is a list of named values.
EthLib writes each list in Lean, and a typo in one value would change every rule that reads it.
So the Python suite compares the Lean values with the files that consensus-specs publishes.

The directory `parameters/` holds those files: the mainnet and minimal presets from Phase 0 to Fulu, and the mainnet and minimal configurations.
They come from `ethereum/consensus-specs` at commit `84454a9d57f4f49f74c78e9f375347baf30474f2`, the release `v1.7.0-alpha.12`.
Each file keeps its upstream bytes and its upstream path below `parameters/`, and `parameters/SHA256SUMS` records its digest.

`bindings/python/tests/consensus/test_parameters.py` reads them and runs three comparisons:

- Each preset in Lean holds every value of the preset files, under the same name.
- Each configuration in Lean holds every value of its file up to Fulu.
  The gossip message ID defines the two message domains of the file as constants, so the configuration leaves them out.
- At each fork from Phase 0 on, the parameters in Lean hold each value that a fork replaces.
  Each one is the value of the latest fork that names it.

A replacement carries the name of its fork as a suffix, such as `INACTIVITY_PENALTY_QUOTIENT_ALTAIR` in the Altair preset.
One suffixed value is new rather than a replacement: `MAX_EFFECTIVE_BALANCE_ELECTRA`, the largest effective balance of a compounding validator.
The suite fails on any other suffixed value, so a replacement that Lean does not hold cannot pass unnoticed.

The directory `networking/` holds the custody vectors of Fulu from the test release `v1.7.0-alpha.12` of `ethereum/consensus-specs`, built at the same commit `84454a9d57f4f49f74c78e9f375347baf30474f2`.
They are the cases of the handlers `get_custody_groups` and `compute_columns_for_custody_group`, copied byte for byte under their path in `mainnet.tar.gz`.
The release repeats the same cases for Gloas and Heze, with only the fork name changed, so the directory keeps those of Fulu.
`bindings/python/tests/consensus/test_custody.py` runs each case through the Lean definitions.
