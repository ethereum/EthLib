# Test format: VRF tree verification

Verify an opening of the VRF tree at an index, under a root: `vrf.Verify` of EIP-8450.

## Test case format

```yaml
input:
  root: Bytes32 -- the root of the tree
  index: int -- the index of the opening
  opening: Bytes1056 -- the secret, then 32 siblings from the leaf up to the root
output: Bytes32 | null -- the output at the index, or null when the opening is rejected
```

All bytes are hex strings prefixed with `0x`.

## Condition

An opening verifies when the path from the leaf of its secret, ordered by the bits of the index, reaches the root.
The output is then the output hash of the secret.

A root of another length than 32 bytes, an opening of another length than 1056 bytes, and an index from `2^32` on are rejected.

The cases named `wrong_secret` flip the low bit of the first byte of the secret.
The cases named `wrong_sibling` flip the low bit of the last byte of the top sibling.
The cases named `other_index` verify the opening at the neighbouring index.

## Sources

The two valid openings follow byte patterns.
Their roots and outputs were computed outside EthLib, by an independent implementation of the specification.
The rejections come from the code under test.
