# Vendored RLP tests

`rlptest.json` holds 28 items and their RLP encodings.
`invalidRLPTest.json` holds 26 byte strings that encode no item.
`example.json` holds one byte string that must decode.

- Repository: [`ethereum/tests`](https://github.com/ethereum/tests)
- Commit: `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`
- Files: `RLPTests/rlptest.json`, `RLPTests/invalidRLPTest.json`, `RLPTests/RandomRLPTests/example.json`
- Authors: the Ethereum Foundation
- Licence: MIT, under the notice below

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The invalid cases do not say why each input is invalid.
The test names the fault of each case from the name of the case.

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
