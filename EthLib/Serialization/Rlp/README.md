# RLP

Recursive Length Prefix (RLP) is the serialization of the execution layer.

Block headers, transactions, receipts and trie nodes are written with it.

The source is Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

## Reading this module

The executable specification and the proofs about it live in two separate trees.

```text
EthLib/Serialization/Rlp/         the executable specification
EthLib/Serialization/Proofs/Rlp/  the machine-checked properties of it
```

An implementer reads `Rlp/` and stops there.

[Proven properties](#proven-properties) says in prose what the other tree establishes.

## The encoding

An item is a byte string or a list of items.

Its encoding is a prefix, then a payload.

The payload of a byte string is its bytes.

The payload of a list is the encodings of its items, one after another.

A single byte below `0x80` is the one exception: it is its own encoding.

The first byte of the prefix says what follows:

- `0x00` to `0x7f`: that byte alone is a byte string of length 1.
- `0x80` to `0xb7`: a byte string of `first - 0x80` bytes, under 56.
- `0xb8` to `0xbf`: a byte string whose length is written on the next `first - 0xb7` bytes.
- `0xc0` to `0xf7`: a list whose payload has `first - 0xc0` bytes, under 56.
- `0xf8` to `0xff`: a list whose payload length is written on the next `first - 0xf7` bytes.

A length is written in base 256, most significant byte first, with no leading zero byte.

A scalar, a non-negative integer, is encoded as the byte string of its digits in base 256, with no leading zero.

So 0 is the empty byte string, and 1024 encodes as `82 04 00`.

## Bounds

A payload must have fewer than `2^64` bytes, as the Yellow Paper asks.

So its length has at most 8 bytes, and the first byte of a long byte string is at most `0xbf`.

The encoding returns an error for a longer payload, instead of a prefix that would read as a list.

## Proven properties

- The big-endian bytes of a number read back as that number.
- They have no leading zero byte.
- No other bytes have both properties, so they are `BE` of the Yellow Paper.
- A length below `2^64` writes a first byte that never wraps around 256.
- The encoding refuses every payload of `2^64` bytes or more.
- The encoding matches every case of `RLPTests/rlptest.json` in [`ethereum/tests`](https://github.com/ethereum/tests/blob/c67e485ff8b5be9abc8ad15345ec21aa22e290d9/RLPTests/rlptest.json).
