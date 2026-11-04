# RLP

Recursive Length Prefix (RLP) is the serialization of the execution layer.
Block headers, transactions, receipts and trie nodes are all written with it.
Many hashes of the chain, such as the hash of a block header, are taken over RLP bytes.
Two clients that encode one object differently would compute different hashes.
So the encoding must be unique, and every client must reject what is not an encoding.

The source is Appendix B of the Yellow Paper, Shanghai version, in
[`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

## Reading this module

The executable specification and the proofs about it live in two separate trees.
`EthLib/Serialization/Rlp/` holds the executable specification.
`EthLib/Serialization/Proofs/Rlp/` holds the machine-checked properties of it.
An implementer reads `Rlp/` and stops there.
[Proven properties](#proven-properties) says in prose what the other tree establishes.

## The encoding

RLP encodes *items*, where an item is either a byte string or a list of items.
The encoding of an item is a prefix followed by a payload.
The payload of a byte string is its bytes.
The payload of a list is the encodings of its items, one after another.
The one exception is a single byte below `0x80`, which is its own encoding, with no prefix.

The first byte of an encoding says what follows:

- `0x00` to `0x7f`: that byte alone is a byte string of length 1.
- `0x80` to `0xb7`: a byte string of `first - 0x80` bytes, under 56.
- `0xb8` to `0xbf`: a byte string whose length is written on the next `first - 0xb7` bytes.
- `0xc0` to `0xf7`: a list whose payload has `first - 0xc0` bytes, under 56.
- `0xf8` to `0xff`: a list whose payload length is written on the next `first - 0xf7` bytes.

A length is written in base 256, most significant byte first, with no leading zero byte.

Take the byte string `dog`, the three bytes `64 6f 67`.
It is shorter than 56 bytes, so its prefix is `0x80 + 3 = 0x83`, and its encoding is `83 64 6f 67`.
The list `[cat, dog]` has a payload of two such encodings, `83 63 61 74` and `83 64 6f 67`.
That payload is 8 bytes, so the prefix is `0xc0 + 8 = 0xc8`.
The encoding of the list is `c8 83 63 61 74 83 64 6f 67`.

A *scalar* is a non-negative integer.
It is encoded as the byte string of its digits in base 256, with no leading zero.
So 0 is the empty byte string, and 1024 = 4 * 256 encodes as `82 04 00`.
A byte string with a leading zero byte holds no scalar.
So the scalar decoder rejects `00` and `82 00 01`, as the Yellow Paper asks.

## Bounds

The Yellow Paper asks that a payload have fewer than `2^64` bytes.
Its length then fits in at most 8 bytes.
So the first byte of a long byte string is at most `0xb7 + 8 = 0xbf`.
A longer payload would need a first byte of `0xc0` or more, which reads as a list.
The encoding therefore returns an error for such a payload instead of a prefix.

## The decoding

The Yellow Paper defines only the encoding, so the decoder accepts exactly its outputs.
Every item has one encoding, so two decoders that follow this rule agree on every input.

The decoder rejects each of the following, each with its own error:

- A byte below `0x80` written with a prefix, as `81 05` for `05`.
- A length below 56 written in the long form, as `b8 03` for `83`.
- A length written with a leading zero byte, as `b9 00 40` for `b8 40`.
- An input that ends before the bytes its prefix announces.
- Bytes left after the item.

## Typed values

A transaction or a block header is not an item but a structure of typed fields.
A *codec* gives each type its item, and reads an item back as a value of the type.
An integer is a scalar whose size its type bounds, so a word has at most 32 bytes.
A fixed-length byte string, such as an address, must have exactly its length.
A list holds the item of each element, and a structure is the list of its fields in order.
The recipient of a transaction is an address, or the empty byte string for a contract creation.

Some structures gain fields at forks, such as the block header at London.
A field that a fork adds has an item only from that fork on.
So the count of items of a block header depends on the fork.

Each typed decoder is strict as well.
It rejects a value too large for its type and a byte string of the wrong length.
It also rejects a list where a byte string belongs, and the reverse.
So `02` holds the integer 2 but no boolean, and `81 ff` holds a byte but no address.

## Proven properties

The proofs start with the big-endian bytes `BE(n)` of a number.
They are the building block of every length and every scalar.
These bytes read back as `n`, and they have no leading zero byte.
No other bytes have both properties, so the code computes the function `BE` of the Yellow Paper.
A length below `2^64` writes a first byte that never wraps around 256.

The encoding refuses every payload of `2^64` bytes or more, and succeeds on every other item.
It matches every case of `RLPTests/rlptest.json` in [`ethereum/tests`](https://github.com/ethereum/tests/blob/c67e485ff8b5be9abc8ad15345ec21aa22e290d9/RLPTests/rlptest.json).

The decoder rejects each of the five non-canonical forms in §4.2.1 of
[Coglio](https://doi.org/10.4204/EPTCS.327.11), whatever bytes follow them.

The central result is that decoding undoes encoding.
The encoding of every item decodes to that item, so two items never share an encoding.
No encoding is a proper prefix of another.
So a sequence of encodings splits into items in only one way.
An encoding followed by more bytes is rejected, and the error carries the count of bytes left over.

The converse holds too: the decoder accepts only canonical input.
Every input that it accepts is the encoding of what it decodes to.
Together, the two directions make the encoding a bijection between items and accepted inputs.
So two decoders that follow the specification agree on every input.

For streams, the parser reads the same item from a longer input and leaves the extra bytes.
So a stream of items needs no end marker.

A scalar decodes exactly from its encoding, and a byte string with a leading zero holds no scalar.
Every scalar below `2^256` has an encoding.

Each typed codec reads back every value it writes, and writes back every item it reads.
So a typed decoder accepts a byte string for a value exactly when it encodes that value.

Finally, the decoding matches every case of `RLPTests/rlptest.json`, and rejects every case of [`RLPTests/invalidRLPTest.json`](https://github.com/ethereum/tests/blob/c67e485ff8b5be9abc8ad15345ec21aa22e290d9/RLPTests/invalidRLPTest.json).
