# Vendored trie tests

Each case of these four files sets keys one after another, starting from an empty trie, and gives the root.
`trietest.json` and `trieanyorder.json` are for the plain trie, and the two `secureTrie` files for the secured trie.

- Source: `TrieTests/` in [`ethereum/tests`](https://github.com/ethereum/tests) at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`.
- Authors: the Ethereum Foundation.
- Licence: the MIT License, under the notice below.

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

A `null` value removes its key, as the empty byte string does.
A key or a value that starts with `0x` is hex, and any other is ASCII text.

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
