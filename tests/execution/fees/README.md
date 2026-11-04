# Fee vectors from the blockchain tests

`header_pairs.json` holds the fee fields of consecutive block headers from the blockchain tests of the execution specification.

- Repository: [`ethereum/execution-specs`](https://github.com/ethereum/execution-specs)
- Release: `tests@v21.0.2`
- Commit: `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`
- Archive: `fixtures.tar.gz`
- Archive sha256: `e2fa7ea2ea516459f9ab92284b2927892f318f4e1f78ca802cb05a6c3b479ed9`
- Licence: CC0-1.0

The pairs come from every fixture under these paths of `blockchain_tests/`, at each network but the Amsterdam ones:

- `*/london/eip1559_fee_market_change/`
- `*/cancun/eip4844_blobs/excess_blob_gas*/`
- `*/osaka/eip7918_blob_reserve_price/`

Each pair is a parent and a child: the genesis header or the last valid block, then the next block.
A pair keeps the child when it is valid, and when the fixture rejects it for its excess blob gas.
The file holds 2,971 valid children and 1,178 rejected ones.

Each pair keeps the path of its fixture file, its test, the index of the child block and its network.
Its numbers are the gas limit, gas used, base fee, blob gas used, excess blob gas and timestamp of each header, as the fixture gives them.
No code of EthLib computed them.

`extract.py` wrote the file from the unpacked archive, and writes the same bytes again:

```text
python -I extract.py fixtures header_pairs.json
```

The test `bindings/python/tests/fees/test_header_pairs.py` reads the file and never rewrites it.
`SHA256SUMS` pins it.
