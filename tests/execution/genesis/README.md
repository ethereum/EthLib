# The mainnet genesis allocation

`mainnet.json` holds the configuration, the header fields and the allocation of the mainnet genesis block.

- Repository: [`ethereum/execution-specs`](https://github.com/ethereum/execution-specs)
- Release: `tests@v21.0.2`
- Commit: `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`
- File: `src/ethereum/assets/mainnet.json`, copied without change
- Licence: CC0-1.0

The allocation gives a balance to each of 8,893 accounts, and nothing else.

The test `bindings/python/tests/blocks/test_genesis.py` builds the genesis block from this file.
It compares the block with `BasicTests/genesishashestest.json` of `tests/execution/ethereum_tests`, which comes from another repository.
`SHA256SUMS` pins the file.
