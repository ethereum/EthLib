# Transaction tests and the mainnet genesis of ethereum/tests

The files here are the transaction tests of the legacy test repository, and its test of the mainnet genesis block.

- Repository: [`ethereum/tests`](https://github.com/ethereum/tests)
- Commit: `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`
- Files: every file of `TransactionTests/` but two, and `BasicTests/genesishashestest.json`, copied without change to the same path
- Results: 2,938, over 14 networks from Frontier to Prague
- Authors: the Ethereum Foundation
- Licence: MIT, under the notice below

The two files left out are `ttData/String10MbData.json` and `ttData/String10MbDataNotEnoughGAS.json`.
Each holds a transaction with 10 MB of data, and the two weigh 42 MB together.

A test gives the bytes of one transaction and, for each network, the outcome that a client must reach.
The outcome is the hash, the sender and the intrinsic gas of the transaction, or the exception that rejects it.

The test `bindings/python/tests/transactions/test_ethereum_tests.py` reads these files and never rewrites them.
`SHA256SUMS` pins each file.

`BasicTests/genesishashestest.json` gives the RLP form, the state root and the hash of the mainnet genesis block.
The test `bindings/python/tests/blocks/test_genesis.py` builds that block from the allocation in `tests/execution/genesis` and compares all three.

## Where EthLib disagrees

EthLib accepts 43 results that the fixtures reject.
Their transactions have a gas limit of 2^64, or a gas limit times gas price above 2^256 - 1.

The Yellow Paper (Berlin version, section 4.2) types the gas limit and the gas price as scalars below 2^256.
Its section 6.2 checks the up-front cost against the sender's balance, and the gas limit against the gas left in the block.
So a block or a balance rejects these transactions, and no rule rejects one alone.
EIP-7825 caps the gas limit from Fusaka on, after the last fork of these fixtures.

The test asserts that EthLib accepts each of the 43 results, so that a change shows.

One result key of `ttWrongRLP/RLPgasLimitWithFirstZeros.json` is misspelt `Cancnun`.
The test reads it as Cancun, the one network that the file lacks.

## Licence

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
