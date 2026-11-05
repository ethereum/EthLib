# Legacy blockchain tests

The files here are blockchain tests of the archived test repository of the proof-of-work era.

- Repository: [`ethereum/legacytests`](https://github.com/ethereum/legacytests)
- Commit: `1f581b8ccdc4c63acf5f2c5c1b155c690c32a8eb`
- Files: the files below `Constantinople/BlockchainTests` and `Cancun/BlockchainTests` that `SHA256SUMS` lists, copied without change to the same path
- Authors: the Ethereum Foundation
- Licence: MIT, under the notice below

A test gives a genesis block and a chain of blocks for one network.
Each block is valid, or names the exception with which a client rejects it.
The directory `Constantinople` fills the networks from Frontier to Constantinople Fix, and the directory `Cancun` fills the later ones.

These files are a small part of the repository, chosen so that each change runs every kind of header and ommer check.
They hold a header error of each kind, and an error in the header of an ommer.
They hold valid ommers, whose rewards are checked, and an ommer error of each kind that the tests fill.
They also hold two transitions to London, and every test of the transition to the DAO Fork.
Three tests seal their blocks with a proof of work.
The weekly parity job runs every test from Frontier to London, from the archive that `tests/sources.toml` pins.
That job also checks that each file here is the file of the archive.

The tests `bindings/python/tests/blocks/test_legacy.py` and `bindings/python/tests/parity/test_legacy.py` read these files and never rewrite them.
`SHA256SUMS` pins each file.

## Where EthLib disagrees

EthLib accepts the block of `GasLimitHigherThan2p63m1.json`, which the tests reject.
Its gas limit is 2^63, just above the gas limit of its parent, 2^63 - 1.
Clients cap the gas limit at 2^63 - 1.
The Yellow Paper (Shanghai version, sections 4.4.3 and 4.4.4) makes the gas limit a natural number, bounded only by the gas limit of the parent and by 5000 from below.
`tests/parity/disagreements.toml` lists each of these cases, so a test fails if EthLib starts to reject them.

EthLib rejects valid blocks 5 to 10 of `londonUncles.json`, at the transition from Berlin to London at block 5.
Each holds the ommer number 4, a Berlin header of 15 fields, while the block is a London header of 16 fields.
EthLib reads the ommers of a block, and the recent blocks of the ommer check, in the form of the block's fork.
EIP-1559 adds the base fee to the headers from the fork block on, so the header of block 4 has none.

The tests of the DAO Fork start it at block 5, so blocks 5 to 14 must carry the extra data `dao-hard-fork`.
`DaoTransactions_UncleExtradata.json` rejects blocks 7, 8 and 10, whose own headers carry it.
Each holds an ommer numbered in that window whose extra data is another value.
EthLib checks the extra data of a block's header, and its ommer check does not yet apply the rule.
EIP-779 asks the extra data of the blocks of the window, and does not mention ommers.

## Licence

```text
Copyright 2014 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
