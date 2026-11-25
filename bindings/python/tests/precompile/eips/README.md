# Precompile cases of EIP-2537 and EIP-7951

The BLS12-381 cases of EIP-2537 and the P256VERIFY cases of EIP-7951 that the precompile tests read, taken from the assets of both EIPs.

- Repository: [`ethereum/EIPs`](https://github.com/ethereum/EIPs)
- Commit: `b055feec322fbc37e9d77a393a50b3ff56b31c92`
- Files: `assets/eip-2537/*.json` and `assets/eip-7951/test-vectors.json`
- Licence: CC0-1.0

`SHA256SUMS` pins the three files.

The files keep the cases of the assets, in their order, with only the fields that the tests read:

- `eip2537_cases.json` holds the 110 cases that succeed and the 81 cases that fail, keyed by the name of their asset file.
  It leaves out the MSM cases with more than 8 pairs.
- `eip2537_msm_repeated.json` holds those MSM cases, 141 for G1 and 141 for G2.
  Each of their inputs repeats one pair from 9 to 149 times, the point at infinity with the scalar 0.
  So the file keeps that pair once for each precompile, and each case keeps its pair count.
- `eip7951_cases.json` holds the 781 cases of EIP-7951, without their price.
  The asset gives each case a price of 3450 gas, but EIP-7951 sets the price at 6900 gas.
  The tests use 6900; [ethereum/EIPs#12536](https://github.com/ethereum/EIPs/pull/12536) proposes to correct the asset.

`extract_eip_cases.py` writes the three files again from the assets, byte for byte:

```text
python -I extract_eip_cases.py <EIPs>/assets .
```
