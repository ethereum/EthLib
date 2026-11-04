# SSZ test vectors of ssz-specs

The files here are the test vectors of the SSZ specification repository.

- Repository: [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs)
- Release: `v0.1.0`
- Commit: `7bce07ff7d51b1a3c66ff4e2bd3233ac248ede70`
- Archive: `ssz-test-vectors-v0.1.0.tar.gz`
- Archive sha256: `e2a65f032b59835c26127295293ea1bc07d7ca0ea1fe0e4f1128dffed333f878`
- Files: every file under `fixtures/ssz/ssz/` in the archive, copied without change to the same path
- Cases: 117
- Authors: the Ethereum Foundation
- Licence: MIT, under the notice below

A case names a type, and gives a value, its SSZ bytes and its hash tree root.
A rejected case gives bytes that no value of the type has, and the reason for the rejection.

The fixtures name each type but do not define it.
The test `bindings/python/tests/ssz/test_ssz_specs.py` writes each type out from the filler classes under `tests/fillers/ssz/` at the same commit.
It reads these files and never rewrites them.
`SHA256SUMS` pins each file.

```text
MIT License

Copyright (c) 2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
