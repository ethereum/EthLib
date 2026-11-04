# Vendored key-address test

The private keys and addresses of `ethereum/tests`, copied byte for byte.

- File: `BasicTests/keyaddrtest.json`
- Repository: [`ethereum/tests`](https://github.com/ethereum/tests)
- Commit: `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`
- Authors: the Ethereum Foundation
- Licence: MIT, under the notice below

`SHA256SUMS` pins the file.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

Each of the two cases gives a private key, its address and a field `sig_of_emptystring`.
The test checks the address of each key.
The file does not say which hash the signature signs.
Neither signature recovers its key's address under the Keccak-256, SHA-256 or SHA3-256 of the empty string, or under the zero hash.
`py_ecc` agrees for the Keccak-256 of the empty string.
So the test does not read the field.

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
