# Test format: VRF tree secret

Compute the secret of an index, from a 32-byte seed.

## Test case format

```yaml
input:
  seed: Bytes32 -- the seed of the tree
  index: int -- the index, below 2^32
output: Bytes32 -- the secret
```

All bytes are hex strings prefixed with `0x`.

## Condition

The secret of index `i` is `keccak256(PQ_VRF_SECRET | seed | LE32(i))`, with `LE32(i)` the index on 4 bytes, least significant first.

The result must match `output`.

## Sources

The seed follows a byte pattern: byte `k` is `17 k + 9 mod 256`.
The expected values were computed outside EthLib, by an independent implementation of the specification.
