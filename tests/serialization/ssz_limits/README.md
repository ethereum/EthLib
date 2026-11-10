# SSZ vectors of lists with very large limits

A decoder compares the length of its input with the limit of a list times the size of an element.
The same product sets the depth of the tree under the hash tree root.
For a large limit, that product wraps in a 32-bit or 64-bit integer.
A decoder that computes it in such an integer then rejects valid input, or accepts input that is too long, and its roots have the wrong depth.

The cases here give lists whose byte limit or chunk count reaches 2^32 or 2^64.
Some types stop just below that size, and others just pass it.
Others have the largest limit that a 32-bit or 64-bit integer holds, 2^32 - 1 or 2^64 - 1.
Then the rounding of the limit up to whole bytes or chunks, or the size of the largest encoding, overflows instead.
Each type is small to use: its values have at most nine elements.
The `ssz_generic` vectors of consensus-specs have no limit this large.

An independent SSZ implementation writes them: the Python package of the SSZ specification repository.

- Package: `eth-ssz-specs` 0.1.0 on PyPI
- Wheel sha256: `466c6cef854cca45022a7cdc3922dd636e30b1a1dd5385845819e3d45ddddf41`
- Repository: [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs)
- Release: `v0.1.0`
- Commit: `7bce07ff7d51b1a3c66ff4e2bd3233ac248ede70`

`generate.py` does not import EthLib, and every run writes the same file:

```bash
uv run --no-project --python 3.12 --with eth-ssz-specs==0.1.0 \
  python -I tests/serialization/ssz_limits/generate.py tests/serialization/ssz_limits
```

`cases.json` lists the cases.
Each case names its type by its kind (`list`, `byte_list` or `bitlist`), the width of an element in bytes, and its limit.
It says what the limit reaches, such as `2^64 bytes`.
A valid case gives the elements of a value, its bytes and its hash tree root.
An invalid case gives bytes that encode no value of the type, the reason, and its root is `null`.
The reason is `partial_element` for a length that is not a whole number of elements, and `empty` or `no_delimiter` for a bitlist without its delimiter bit.
The package rejects each invalid case before the script writes it.

A list of one-byte elements has no invalid case, since every length is a whole number of elements.
No case goes over its limit, since that would take an input of at least 2^29 bytes.

The package roots an empty subtree of at most 2^64 leaves, so no case has more than 2^64 chunks.

`bindings/python/tests/ssz/test_ssz_limits.py` checks that EthLib encodes, decodes and roots each value as the file gives, and rejects each invalid input.

`SHA256SUMS` pins each file.
