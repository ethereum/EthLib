# Vendored Ethash specification

`index.md.txt` is the Ethash specification of the Ethereum Foundation, as ethereum.org publishes it.
It is the file `index.md` below, renamed so that the Markdown checks of the repository skip it.
Its appendix lists the dataset and cache sizes of the first 2048 epochs, which the tests read.

- Repository: [`ethereum/ethereum-org-website`](https://github.com/ethereum/ethereum-org-website).
- Commit: `0899bcb4dcb12040ccf46bea0053a422812bf913`.
- File: `public/content/developers/docs/consensus-mechanisms/pow/mining/mining-algorithms/ethash/index.md`.
- Authors: the contributors to ethereum.org.
- Licence: the MIT License, under the notice below.

The file is copied byte for byte, and `SHA256SUMS` pins it.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

```text
Copyright (c) 2019-2026 ethereum.org contributors

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
