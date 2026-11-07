# Vendored proof tests

Each `.io` file is one `eth_getProof` request and its response, from `tests/eth_getProof/`.
The response holds the proof of one account, and `get-account-proof-with-storage.io` also holds the proof of one storage slot of that account.

- Source: [`ethereum/execution-apis`](https://github.com/ethereum/execution-apis) at commit `3284ee80c3da3e516c53782dde75157cccf1ebdc`.
- Authors: the contributors of `ethereum/execution-apis`.
- Licence: CC0 1.0 Universal.

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The files hold no state root, so the tests state the root that each account proof starts from.
All five start from one root, the hash of their first node.
It is the state root of block 60 of the test chain `tests/chain.rlp` at the same commit.
