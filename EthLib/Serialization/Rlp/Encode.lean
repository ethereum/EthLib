import EthLib.Serialization.Rlp.Item

/-!
# `Serialization.Rlp.Encode`

The RLP encoding of an item, as Appendix B of the Yellow Paper (Shanghai version, `ethereum/yellowpaper` at `efc5f9a`) defines it.

An encoding is a prefix, then a payload.

The payload of a byte string is its bytes, and the payload of a list is the encodings of its items, one after another.

The one exception is a single byte below `0x80`, which is its own encoding, with no prefix.

A byte string or a list is short when its payload has fewer than 56 bytes.

The first byte of an encoding alone tells a byte string from a list, and a short one from a long one:

```text
    0x00..0x7f   a single byte below 0x80 is its own encoding
    0x80..0xb7   short string: 0x80 + length, then the bytes
    0xb8..0xbf   long string:  0xb7 + length of the length, the length, then the bytes
    0xc0..0xf7   short list:   0xc0 + payload length, then the payload
    0xf8..0xff   long list:    0xf7 + length of the length, the length, then the payload
```

For example:

```text
    [ "cat", "dog" ]  ->  c8 | 83 63 61 74 | 83 64 6f 67
```

A long byte string or list writes the length of its payload as `BE(length)`: in base 256, with no leading zero byte.

The length must be below `2^64`, so `BE(length)` takes at most 8 bytes.

That keeps the first byte of a long string at most `0xb7 + 8 = 0xbf`, below every list.

It also keeps the first byte of a long list at most `0xf7 + 8 = 0xff`, which is still a byte.

A payload of `2^64` bytes or more has no encoding.

The execution specs use `ethereum/ethereum-rlp`, and its `src/ethereum_rlp/rlp.py` at v0.1.6 encodes by the same rules.

It has no check for the `2^64` bound, which no byte string in memory reaches.
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

```text
    length < 56      [ offset + length ]
    length < 2^64    [ offset + 55 + k | BE(length) ]
    otherwise        no encoding
```

Here `offset` is `kind.offset`, and `k` is the number of bytes of `BE(length)`.

The Yellow Paper writes `offset + 55` as 183 for a byte string and 247 for a list. -/
def lengthPrefix (kind : PayloadKind) (length : Nat) : Except RlpError ByteArray :=
  if length < 56 then
    .ok ⟨#[UInt8.ofNat (kind.offset + length)]⟩
  else if length < 2 ^ 64 then
    -- Below `2^64`, `BE(length)` has at most 8 bytes, so the first byte is at most `0xc0 + 63 = 0xff`.
    let lengthBytes := bigEndian length
    .ok (⟨#[UInt8.ofNat (kind.offset + 55 + lengthBytes.size)]⟩ ++ lengthBytes)
  else
    .error (.payloadTooLong length)

/-- Whether `data` is a single byte below `0x80`: then it is its own encoding. -/
def isSingleLowByte (data : ByteArray) : Bool :=
  if h : data.size = 1 then decide (data[0] < 0x80) else false

/-- `R_b` of the Yellow Paper: the encoding of a byte string. -/
def encodeBytes (data : ByteArray) : Except RlpError ByteArray :=
  if isSingleLowByte data then
    .ok data
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
  | item :: rest => do
      let head ← encode item
      let tail ← joinEncodings rest
      return head ++ tail
  termination_by structural items => items

end

end EthLib.Serialization.Rlp
