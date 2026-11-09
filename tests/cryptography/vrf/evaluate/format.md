# Test format: VRF tree evaluate

Compute the output of an index, from a 32-byte seed.

## Test case format

```yaml
input:
  seed: Bytes32 -- the seed of the tree
  index: int -- the index, below 2^32
output: Bytes32 -- the output
```

All bytes are hex strings prefixed with `0x`.

## Condition

The output of index `i` is `keccak256(PQ_VRF_OUTPUT | LE32(i) | s_i)`, with `s_i` the secret of index `i`.
Here `LE32(i)` is the index on 4 bytes, little-endian.

The result must match `output`.

## Sources

The seed follows a byte pattern: byte `k` is `17 k + 9 mod 256`.
The expected values were computed outside EthLib, by an independent implementation of the specification.
