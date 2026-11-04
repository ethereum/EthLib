# Test format: Keccak-f[1600] permutation

Apply Keccak-f[1600], the permutation of FIPS 202 §3.4, to a state.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  state: State -- the state before the permutation
output: State -- the state after the permutation
```

- `State` is a 200-byte string, in hexadecimal, prefixed with `0x`.
- Lane `i` of the state is bytes `8i` to `8i + 7`, the first least significant, as in FIPS 202 §3.1.3.

## Condition

The `permutation` handler applies Keccak-f[1600] to `state`.

The result must match `output`.

## Sources

The 2 cases are the examples of `KeccakPermutationIntermediateValues.txt` in the Keccak team's `KeccakKAT-3.zip`.
The first permutes the all-zero state, and the second permutes the output of the first.
`bindings/python/tests/keccak/kat/README.md` gives the location and the digest of that archive.
