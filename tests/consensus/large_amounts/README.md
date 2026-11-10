# Consensus vectors with amounts above 2^53 and sums past 2^64 - 1

A 64-bit float holds every integer only up to 2^53 = 9,007,199,254,740,992.
Between 2^53 and 2^54 it holds only even integers, and higher up only multiples of 4, 8 and so on.
For example, 2^53 + 1 = 9,007,199,254,740,993 reads back from a float as 9,007,199,254,740,992.
An implementation that reads or keeps a uint64 amount in a float rounds such a value, so its balances and its state roots drift.
The cases of consensus-specs use realistic amounts, so almost no balance, deposit or withdrawal reaches that range.
Effective balances test none of this: they are multiples of 10^9, and a float holds every such multiple exactly up to 2^62.

The cases here give results that are odd integers above 2^53, and sums that pass 2^64 - 1.
A step whose uint64 passes 2^64 - 1 is invalid, so such a case has no post state.

- A Deneb deposit tops up a balance by 2^53 + 1, to an odd balance above 2^53, or to exactly 2^64 - 1.
  In a third case the top-up would pass 2^64 - 1.
- At Heze a pending deposit tops up a balance the same way at the epoch transition, in the same three cases.
  In a fourth case the churn that the epoch may apply would pass 2^64 - 1.
- A partial withdrawal takes an excess balance of 2^53 + 1, at Deneb and at Heze.
  At Heze two pending payments of 2^63 Gwei to one builder sum to 2^64.
  At Deneb a withdrawal only lowers a balance, so it has no such case.
- A proposer slashing slashes a validator whose balance is odd and above 2^53, at Deneb and at Heze.
  In another case the proposer already holds 2^64 - 1 Gwei, so its reward would pass that.
- At the epoch transition, 2^63 Gwei of recent slashings times the multiplier 3 passes 2^64 - 1, at Deneb and at Heze.
- The rewards of an epoch go to balances that start above 2^53 and end odd, at Deneb and at Heze.
  In another case one balance already holds 2^64 - 1 Gwei and earns a reward.

EthLib rejects each invalid case as an arithmetic overflow, and `bindings/python/tests/consensus/test_large_amounts.py` checks that.

## How the cases were produced

The test functions in `generator/large_amounts/` run on the executable specification of consensus-specs.
The specification writes each case in the format of its operations and epoch processing tests.

- Repository: [`ethereum/consensus-specs`](https://github.com/ethereum/consensus-specs)
- Release: `v1.7.0-beta.4`
- Commit: `aa16bb4c156184e9548a997d53efaf2a228a6304`

In a checkout of that commit, link the generator in as a test package, build the specification and run the tests with reference output.
Below, `$ETHLIB` is the root of an EthLib checkout and `$OUT` an empty directory.

```bash
ln -s "$ETHLIB/tests/consensus/large_amounts/generator/large_amounts" \
  tests/core/pyspec/eth_consensus_specs/test/large_amounts
make build
PYTHONDONTWRITEBYTECODE=1 uv run pytest -p no:cacheprovider --preset=minimal \
  --reftests --reftests-output="$OUT" tests/core/pyspec/eth_consensus_specs/test/large_amounts
```

Then copy the `minimal` directory of `$OUT` here; two runs give the same bytes.
Each test function also checks its claim: its results are odd and above 2^53, or the step fails because a uint64 passes 2^64 - 1.
The generator does not import EthLib.
