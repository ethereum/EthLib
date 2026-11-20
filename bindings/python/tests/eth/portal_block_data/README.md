# A mainnet block after Shapella

`block-data-19426587.yaml` holds block 19426587 of mainnet, the first block of Cancun.
It has three lines: the RLP of the header, of the body and of the receipts, each as hexadecimal.
The body holds 37 transactions, no ommers and 16 withdrawals.

- Repository: [`ethereum/portal-spec-tests`](https://github.com/ethereum/portal-spec-tests)
- Commit: `938744a83d4f85dcdcf9bac12b798e15f2eac2b1`
- File: `tests/mainnet/history/block_data/block-data-19426587.yaml`, copied without change
- Licence: MIT, in `LICENSE`

The test `bindings/python/tests/eth/test_bodies.py` checks the body against the header.
It reads the header and the body, and leaves the receipts aside.
The header has the number 19426587 and the activation time of Cancun on mainnet, from EIP-7569.
`SHA256SUMS` pins the file.
