# Vendored genesis tests

`basic_genesis_tests.json` holds three genesis allocations and the RLP of the genesis block that each one gives.
The state root of a block is the fourth field of its header, so each case pins the state root of its allocation.

- Source: `GenesisTests/basic_genesis_tests.json` in [`ethereum/tests`](https://github.com/ethereum/tests) at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`.
- Authors: the Ethereum Foundation.
- Licence: the MIT License, under the notice below.

The file is copied byte for byte, and `SHA256SUMS` pins it.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

One case gives balances under the key `wei` instead of `balance`, and the tests read either key.

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
