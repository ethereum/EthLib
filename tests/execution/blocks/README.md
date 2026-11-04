# Block test vectors

`blockchain_tests.json` holds valid blocks from the blockchain tests of `ethereum/execution-specs`.
They come from the release `tests@v21.0.2`, whose target is commit `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`, under CC0-1.0.
Its archive `fixtures.tar.gz` has sha256 `e2fa7ea2ea516459f9ab92284b2927892f318f4e1f78ca802cb05a6c3b479ed9`.

The cases cover every fork that the release fills, from Frontier to Amsterdam.
For each fork, they hold the genesis block and every valid block of the test `block_intermediate_state`.
Four more tests add blocks with withdrawals, a beacon root, requests and a block access list.

Each case keeps the path of its file in the archive, the name of its test and its network.
Its block and its header hash are copied from the fixture without change, so no code of EthLib computed them.

The Python test `bindings/python/tests/blocks/test_blocks.py` reads these cases and never rewrites them.
