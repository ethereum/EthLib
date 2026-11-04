# Vendored proof test

`get-account-proof-with-storage.io` is one `eth_getProof` request and its response.
The response holds the proof of one account, and the proof of one storage slot of that account.

- Source: `tests/eth_getProof/get-account-proof-with-storage.io` in [`ethereum/execution-apis`](https://github.com/ethereum/execution-apis) at commit `3284ee80c3da3e516c53782dde75157cccf1ebdc`.
- Authors: the contributors of `ethereum/execution-apis`.
- Licence: CC0 1.0 Universal.

The file is copied byte for byte, and `SHA256SUMS` pins it.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The file holds no state root, so the test states the root that the account proof starts from.
It is the state root of block 60 of the test chain `tests/chain.rlp` at the same commit.
