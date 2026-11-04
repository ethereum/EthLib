# MODEXP calls of the EIP-198 state tests

`eip198_calls.json` holds the MODEXP calls of the state test `test_modexp` of the execution specification, with the outcome of each at each fork.

- Repository: [`ethereum/execution-specs`](https://github.com/ethereum/execution-specs)
- Release: `tests@v21.0.2`
- Commit: `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`
- Archive: `fixtures.tar.gz`, sha256 `e2fa7ea2ea516459f9ab92284b2927892f318f4e1f78ca802cb05a6c3b479ed9`
- Fixtures: `state_tests/for_*/byzantium/eip198_modexp_precompile/modexp/modexp.json`
- Licence: CC0-1.0

Each test sends its call data to a contract, which calls MODEXP with all of it and all its gas.
The contract stores 1 in slot 0 when the call succeeds, then creates a contract whose code is the output.
So for each test and network, the post state of the fixture gives the outcome of the call:

- `input`: the data of the transaction, which is the call data of MODEXP;
- `gasLimit`: the gas limit of the transaction, more than the call can get;
- `success`: whether slot 0 of the calling contract holds 1;
- `output`: the code of the created contract when the call succeeds.

The file holds 47 calls at each of 10 networks, from Byzantium to Osaka, and leaves out Amsterdam.
`extract.py` wrote it from the unpacked archive, and writes the same bytes again:

```text
python -I extract.py fixtures eip198_calls.json
```

The test `bindings/python/tests/precompile/test_modexp_state_tests.py` reads the file and never rewrites it.
`SHA256SUMS` pins it.
