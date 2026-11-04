# Vendored difficulty tests

These files hold 18,598 cases of the difficulty of a block before Paris.
Each case gives the parent's timestamp, difficulty and ommer count, the block's number and timestamp, and the expected difficulty.
The key at the top of each file names the fork whose rule applies.
The three `difficultyEIP2384` files run the delay of EIP-2384 under the key `Berlin`, which keeps that delay.

- Repository: [`ethereum/tests`](https://github.com/ethereum/tests).
- Commit: `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`.
- Files: every file of `DifficultyTests/dfArrowGlacier`, `dfByzantium`, `dfConstantinople`, `dfEIP2384`, `dfFrontier`, `dfGrayGlacier` and `dfHomestead`.
- Authors: the Ethereum Foundation.
- Licence: the MIT License, under the notice below.

The files are copied byte for byte, without their directories, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The `BasicTests/difficulty*.json` files of the same commit are not vendored.
Their cases name no fork, so the rule would come from the block number and a schedule of forks.
Some also give a block no later than its parent, which the header checks reject.

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
