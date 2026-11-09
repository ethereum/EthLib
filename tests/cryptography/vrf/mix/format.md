# Test format: VRF tree mix

Mix an output of the VRF tree with randomness revealed after the root is registered.
The mixed value is what a selection compares with its threshold.

## Test case format

```yaml
input:
  output: Bytes32 -- an output of the tree
  randomness: Bytes32 -- randomness that became known after the root was registered
output: Bytes32 -- the mixed value
```

All bytes are hex strings prefixed with `0x`.

## Condition

The mixed value is `keccak256(PQ_VRF_MIX | input.output | input.randomness)`.

The result must match the top-level `output`.

## Sources

The output is the output at index 0 of the valid opening of the `verify` cases.
The randomness follows a byte pattern: byte `k` is `7 k + 1 mod 256`.
The expected value was computed outside EthLib, by an independent implementation of the specification.
