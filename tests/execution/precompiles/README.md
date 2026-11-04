# Precompile vector files of execution-specs

The files here are the vector files that the precompile tests of the execution specification read.

- Repository: [`ethereum/execution-specs`](https://github.com/ethereum/execution-specs)
- Commit: `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`
- Files: every JSON file under a `vector`, `vectors` or `point_evaluation_vectors` directory of `tests/`, at the same path below this directory
- Licence: CC0-1.0

Two files are not copied whole: `msm_G1_bls.json` (3.6 MB) and `msm_G2_bls.json` (6.6 MB).
`msm_up_to_8_pairs.json` holds their cases with at most 8 pairs, 22 and 23, each copied without change.
The larger cases repeat inputs that the EIP-2537 suite already runs.

The files hold:

- the EIP-2537 cases, 110 that succeed and 74 that fail;
- 294 P256VERIFY cases of EIP-7951, drawn from Wycheproof;
- 46 MODEXP cases with the prices of EIP-2565 and EIP-7883, and 32 more with outputs only;
- the 122 point evaluation cases of EIP-4844, the same as `tests/cryptography/kzg/verify_kzg_proof`.

The test `bindings/python/tests/precompile/test_execution_specs_vectors.py` reads these files and never rewrites them.
`SHA256SUMS` pins each file.
