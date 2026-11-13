# Vendored JSON-RPC tests

Each `.io` file is one request of the execution JSON-RPC API and its response, from `tests/<method>/` of the source.
These directories keep the layout of the source, one directory for each method.

The directory `error-groups` holds the groups of error codes of the API, from `src/error-groups/` of the source.

- Source: [`ethereum/execution-apis`](https://github.com/ethereum/execution-apis) at commit `3284ee80c3da3e516c53782dde75157cccf1ebdc`.
- Authors: the contributors of `ethereum/execution-apis`.
- Licence: CC0 1.0 Universal.

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The files `genesis.json`, `chain.rlp`, `forkenv.json` and `headfcu.json` are the test chain of the source, from `tests/`.
The chain is a genesis state and 60 blocks, and the forkchoice update names block 60 as head, safe and finalized.
The tests replay it through the state transition into a chain view, and send the requests of the methods that the view serves.
They compare a result as a JSON value, and an error by its code, and by its data where the file gives it.
A file marked `speconly` is checked against the schema of the result only, as `docs-api/docs/tests.md` of the source says.

The files of the other methods run through the readers of the parameters, without a chain.

The files of the `debug_` methods and of `eth_getStorageAt` answer with an error, because a reader rejects a parameter.
The tests compare only the code of that error, since the source fixes the code of an error and not its message.

The other files name a block by an object of EIP-1898, or by a hash written as a string.
The tests check how the reader reads that block parameter.
They do not check the result of the request, which needs the chain of the source.

The tests compare the error codes of the bindings with these groups.
They take the order of the groups from the table of reserved ranges in `src/error-groups/README.md` of the source.
