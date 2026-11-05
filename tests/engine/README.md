# Engine API test vectors

`new_payload.json` holds calls of `engine_newPayload` from the engine blockchain tests of `ethereum/execution-specs`.
They come from the release `tests@v21.0.2`, whose target is commit `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`, under CC0-1.0.
Its archive `fixtures.tar.gz` has sha256 `e2fa7ea2ea516459f9ab92284b2927892f318f4e1f78ca802cb05a6c3b479ed9`.

The cases come from the directory `blockchain_tests_engine`, for the networks from Paris to BPO2.
They hold every payload that expects a JSON-RPC error.
They hold every payload that the checks before execution reject: a wrong block hash, a transaction that does not decode, or a wrong structure.
They also hold the first six valid payloads of each network whose parameters have at most 8,000 bytes of JSON.
Of the large rejected payloads, they keep the first one for each expected exception.

Each case keeps the path of its file in the archive, the name of its test, the index of the payload and its network.
Its method, its parameters, its expected exception and its expected error code are copied from the fixture without change.

`extract_new_payload.py` wrote the file from the directory, unpacked from the archive, and writes the same bytes again:

```text
python -I extract_new_payload.py <directory blockchain_tests_engine> new_payload.json
```

`forkchoice.json` holds chains of the same directory, for `engine_forkchoiceUpdated`.
For each network, it keeps the three tests with the most payloads, among those with at least three payloads or an invalid one.
Each chain keeps the hash of its genesis block, the hash and the parent hash of each payload, and the last block hash of the test.
A payload counts as valid when the fixture expects neither an exception nor an error code.
`extract_forkchoice.py` wrote the file in the same way:

```text
python -I extract_forkchoice.py <directory blockchain_tests_engine> forkchoice.json
```

The Python tests in `bindings/python/tests/engine/` read these cases and never rewrite them.
A test marked `archive` runs every payload of the directory.
