import EthLib.Serialization.Rlp.Item

/-!
# `Serialization.Rlp.Encode`

The RLP encoding of an item.

Source: Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex), equations for `R_b`, `R_l` and `s`.

An encoding is a prefix, then a payload.

The payload of a byte string is its bytes.

The payload of a list is the encodings of its items, one after another.

A single byte below `0x80` is the one exception: it is its own encoding, with no prefix.

A payload is short when it has fewer than 56 bytes.

The first byte of an encoding tells a byte string from a list, and a short payload from a long one:

- `0x00` to `0x7f`: a single byte below `0x80`, which is its own encoding.
- `0x80` to `0xb7`: a short byte string, with `0x80 + length`.
- `0xb8` to `0xbf`: a long byte string, with `0xb7` plus the size of `BE(length)`, then `BE(length)`.
- `0xc0` to `0xf7`: a short list, with `0xc0 + length`.
- `0xf8` to `0xff`: a long list, with `0xf7` plus the size of `BE(length)`, then `BE(length)`.

For example, the list of "cat" and "dog" encodes as:

```text
[ c8 | 83 63 61 74 | 83 64 6f 67 ]
```

A length must be below `2^64`, so `BE(length)` has at most 8 bytes.

That keeps the first byte of a long byte string at most `0xb7 + 8 = 0xbf`, below every list.

It also keeps the first byte of a long list at most `0xf7 + 8 = 0xff`, which is still a byte.

A payload of `2^64` bytes or more has no encoding.
-/

namespace EthLib.Serialization.Rlp

/-- What a payload holds: the bytes of a byte string, or the encodings of the items of a list. -/
inductive PayloadKind where
  /-- The bytes of a byte string. -/
  | bytes
  /-- The encodings of the items of a list. -/
  | list

/-- The first byte of the prefix of an empty payload: `0x80` for a byte string, `0xc0` for a list. -/
def PayloadKind.offset : PayloadKind → Nat
  | .bytes => 0x80
  | .list => 0xc0

/-- The prefix of a payload of `length` bytes.

- Below 56 bytes, it is the one byte `offset + length`.
- Below `2^64` bytes, it is the byte `offset + 55 + k`, then `BE(length)` on its `k` bytes.
- From `2^64` bytes on, there is no prefix.

The offset is `0x80` for a byte string and `0xc0` for a list.

The Yellow Paper writes `offset + 55` as 183 for a byte string and 247 for a list. -/
def lengthPrefix (kind : PayloadKind) (length : Nat) : Except RlpError ByteArray :=
  if length < 56 then
    .ok ⟨#[UInt8.ofNat (kind.offset + length)]⟩
  else if length < 2 ^ 64 then
    -- Below `2^64`, `BE(length)` has at most 8 bytes, so the first byte is at most `0xc0 + 55 + 8 = 0xff`.
    let lengthBytes := bigEndian length
    .ok (⟨#[UInt8.ofNat (kind.offset + 55 + lengthBytes.size)]⟩ ++ lengthBytes)
  else
    .error (.payloadTooLong length)

/-- Whether `data` is a single byte below `0x80`: then it is its own encoding. -/
def isSingleLowByte (data : ByteArray) : Bool :=
  if h : data.size = 1 then decide (data[0] < 0x80) else false

/-- `R_b` of the Yellow Paper: the encoding of a byte string. -/
def encodeBytes (data : ByteArray) : Except RlpError ByteArray :=
  -- One byte below `0x80` is its own encoding.
  if isSingleLowByte data then
    .ok data
  -- Any other byte string takes the prefix of its length.
  else do
    return (← lengthPrefix .bytes data.size) ++ data

mutual

/-- `RLP` of the Yellow Paper: the encoding of an item.

It fails only when a payload has `2^64` bytes or more. -/
def encode : Item → Except RlpError ByteArray
  | .bytes data => encodeBytes data
  -- `R_l` of the Yellow Paper: the prefix, then the payload of the list.
  | .list items => do
      let payload ← joinEncodings items
      return (← lengthPrefix .list payload.size) ++ payload
  -- Structural recursion, which the kernel unfolds to evaluate the known answers.
  termination_by structural item => item

/-- `s` of the Yellow Paper: the encodings of `items`, one after another.

It fails when the encoding of one of them fails. -/
def joinEncodings : List Item → Except RlpError ByteArray
  | [] => .ok .empty
  -- Each item's encoding, in order, and a failure if any of them fails.
  | item :: rest => do
      let head ← encode item
      let tail ← joinEncodings rest
      return head ++ tail
  termination_by structural items => items

end

end EthLib.Serialization.Rlp
