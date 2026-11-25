# The Sepolia configuration and its last proof-of-work header

These files give the activations of Sepolia, and the block at which Paris activates there.

`genesis.json` and `config.yaml` come from the network's own repository:

- Repository: [`eth-clients/sepolia`](https://github.com/eth-clients/sepolia)
- Commit: `7b1b9d9549787b6bbf538f943304c4cf84f7e39e`
- Files: `metadata/genesis.json` and `metadata/config.yaml`, copied without change
- Licence: Unlicense

`genesis.json` gives the chain ID, the deposit contract, the fork times and the genesis allocation.

`config.yaml` gives `TERMINAL_BLOCK_HASH`, the hash of the last proof-of-work block of Sepolia.

No published file gives the number of that block.

`terminal_header.rlp` is the RLP of the header of that block.

Its fields come from `eth_getBlockByHash` on a public Sepolia node, encoded as a London header.

The tests authenticate it: its keccak256 must equal `TERMINAL_BLOCK_HASH`.

Its number is 1,450,408, so Paris activates at block 1,450,409, as EIP-3675 sets.

The header cannot show that the block crosses the terminal total difficulty.

That needs the total difficulty of the block and of its parent, which no header carries.

`bindings/python/tests/chain/test_sepolia.py` reads all three files.

`SHA256SUMS` pins them.
