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
Each change also runs every block of these files through the state transition.
The weekly parity job runs every test from Frontier to London, from the archive that `tests/sources.toml` pins.
It also runs the state tests of `ethereum/tests` in blockchain form, from the directories `GeneralStateTests`.
That job also checks that each file here is the file of the archive.

The tests `bindings/python/tests/blocks/test_legacy.py` and `bindings/python/tests/parity/test_legacy.py` read these files and never rewrite them.
`SHA256SUMS` pins each file.

## Where EthLib disagrees

EthLib accepts the block of `GasLimitHigherThan2p63m1.json`, which the tests reject.
Its gas limit is 2^63, just above the gas limit of its parent, 2^63 - 1.
Clients cap the gas limit at 2^63 - 1.
The Yellow Paper (Shanghai version, sections 4.4.3 and 4.4.4) makes the gas limit a natural number, bounded only by the gas limit of the parent and by 5000 from below.
`tests/parity/disagreements.toml` lists each of these cases, for the header check and for the state transition.
So a test fails if EthLib starts to reject them.

The state transition leaves out the network `Constantinople`.
That network runs EIP-1283, which EIP-1716 removed before the fork reached mainnet.
EthLib treats Constantinople as Petersburg, so it would compute other gas costs for these tests.
The header, ommer and DAO Fork checks still run that network, since Petersburg keeps its headers, ommers and rewards.

## Licence

```text
Copyright 2014 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
