# Block test vectors

`blockchain_tests.json` holds valid blocks from the blockchain tests of `ethereum/execution-specs`.
They are pinned to the release `tests@v21.0.3`, whose target is commit `391d8a05d5cb182542ac7e7330c858b6ee03f990`, under CC0-1.0.
Its archive `fixtures.tar.gz` has sha256 `46bd48fb71a23da084218fe856fe442ab0c8d00c85c1c1aead0d2a965804fd24`.

The files without a script, `blockchain_tests.json`, `receipts.json`, `withdrawals.json` and `deposits.json`, were selected from the release `tests@v21.0.2`.
Each of their cases is unchanged in `tests@v21.0.3`, apart from the `_info` of its fixture.

The cases cover every fork that the release fills, from Frontier to Amsterdam.
For each fork, they hold the genesis block and every valid block of the test `block_intermediate_state`.
Four more tests add blocks with withdrawals, a beacon root, requests and a block access list.
Four more add the first valid block with a typed transaction of type 1, 2, 3 or 4, from the test of that type at its fork.

Each case keeps the path of its file in the archive, the name of its test and its network.
Its block and its header hash are copied from the fixture without change, so no code of EthLib computed them.

`receipts.json` holds receipts of valid blocks of the same release, with the Bloom filter that the fixture gives for each.
For each fork, transaction type, and presence or absence of logs, it keeps the first four receipts in path order.

`withdrawals.json` holds the Shanghai tests of `eip4895_withdrawals` whose first block is valid and has no transaction.
Each case keeps the state before the block, as the fixture gives it, and the state roots of the genesis header and of the block header.

`deposits.json` holds the valid Prague blocks of the `eip6110_deposits` tests that have at most 100 logs.
Each case keeps the logs of the receipts of its block, in order, and the requests hash of its header.

`rewards.json` holds, for each network from Frontier to Paris, the tests whose first block is valid and has no transaction.
Each case keeps the state before the block, as the fixture gives it, and the state roots of the genesis header and of the block header.
Before Paris the only change of such a block is the reward of its miner, so its root checks the reward.
`extract_rewards.py` wrote the file from the archive, unpacked from Frontier to Paris, and writes the same bytes again:

```text
python -I extract_rewards.py <directory of fixtures> rewards.json
```

`invalid_headers.json` holds invalid blocks from Paris to Osaka whose exception is a header check.
The checks are the excess blob gas, the gas limit and the base fee.
Each case keeps the header of the block, the header of its parent and the exception of the fixture.
It keeps at most two cases of the excess blob gas from each file.
`extract_invalid_headers.py` wrote the file from the archive, unpacked from Paris to Osaka, and writes the same bytes again:

```text
python -I extract_invalid_headers.py <directory of fixtures> invalid_headers.json
```

`block_access_lists.json` holds the block access list of every Engine API payload of the Amsterdam tests of `eip7928_block_level_access_lists`.
Each case keeps the RLP form of the list, the gas limit of its block and the validation error of the payload, if any.
A valid payload also keeps the access list hash of its block, from the header of the matching blockchain test.
`extract_block_access_lists.py` wrote the file from the archive, unpacked for these tests, and writes the same bytes again:

```text
python -I extract_block_access_lists.py <directory that holds fixtures> block_access_lists.json
```

`blob_schedules.json` holds header pairs of the four test networks that set a blob schedule of their own: `AmsterdamBPOIncrease`, `AmsterdamBPODecrease` and their transitions at time 15,000.
From each file it keeps at most two valid headers and two headers whose exception is the excess blob gas.
Each case keeps the header, its parent, the exception if any, and the blob schedule of the fixture's config.
`extract_blob_schedules.py` wrote the file from the archive, unpacked for these networks, and writes the same bytes again:

```text
python -I extract_blob_schedules.py <directory of fixtures> blob_schedules.json
```

`genesis.json` holds the genesis block of the test `block_intermediate_state` at each network from Frontier to Amsterdam.
Each case keeps the state before the first block and the genesis header in the JSON form of the fixture.
It also keeps the RLP form of the genesis block.
`extract_genesis.py` wrote the file from the archive, unpacked for these tests, and writes the same bytes again:

```text
python -I extract_genesis.py <directory of fixtures> genesis.json
```

The Python tests in `bindings/python/tests/blocks/` read these cases and never rewrite them.
