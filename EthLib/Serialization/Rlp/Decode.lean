import EthLib.Serialization.Rlp.Encode

/-!
# `Serialization.Rlp.Decode`

The strict RLP decoding: the inverse of the encoding, which rejects every other input.

Source: Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

The Yellow Paper defines only the encoding.

So the decoder accepts exactly the outputs of the encoding, and nothing else.

Every item has one encoding, so two decoders that follow this rule agree on every input.

A lax decoder would accept bytes that the encoding never writes.

There are three such forms, each longer than the real encoding:

- a byte below `0x80` written with a prefix, as `81 05` for `05`;
- a length below 56 written in the long form, as `b8 03` for `83`;
- a length written with a leading zero byte, as `b9 00 40` for `b8 40`.

The decoder rejects all three, and any input that ends early or has bytes left after the item.
-/

namespace EthLib.Serialization.Rlp

/-- What the first bytes of an encoding announce, from its first byte `first` and the bytes after it.

The result is the kind of payload, the number `k` of bytes that write the length, and the length.

- From `0x80` to `0xb7`, a byte string of `first - 0x80` bytes, and `k = 0`.
- From `0xb8` to `0xbf`, a byte string whose length is on the next `k = first - 0xb7` bytes.
- From `0xc0` to `0xf7`, a list payload of `first - 0xc0` bytes, and `k = 0`.
- From `0xf8` to `0xff`, a list payload whose length is on the next `k = first - 0xf7` bytes.

A byte below `0x80` is its own encoding and announces nothing, so it is not passed here. -/
def readPrefix (first : UInt8) (rest : List UInt8) : Except RlpError (PayloadKind × Nat × Nat) :=
  -- The short forms write the length in the first byte.
  if first < 0xb8 then
    .ok (.bytes, 0, first.toNat - 0x80)
  else if first < 0xc0 then
    readLongLength .bytes (first.toNat - 0xb7)
  else if first < 0xf8 then
    .ok (.list, 0, first.toNat - 0xc0)
  else
    readLongLength .list (first.toNat - 0xf7)
where
  /-- The long form: the length is `BE(length)` on the next `k` bytes, and is at least 56. -/
  readLongLength (kind : PayloadKind) (k : Nat) : Except RlpError (PayloadKind × Nat × Nat) :=
    -- The `k` bytes of the length must all be there.
    if rest.length < k then
      .error (.inputTooShort k rest.length)
    else
      let lengthBytes := rest.take k
      -- `BE` has no leading zero byte, and `k` is at least 1 here.
      if lengthBytes.head? = some 0 then
        .error .leadingZeroInLength
      else
        let length := ofBigEndian lengthBytes
        -- A length below 56 fits in the first byte, so its long form is never written.
        if length < 56 then
          .error (.longFormForShortLength length)
        else
          .ok (kind, k, length)

mutual

/-- One item read from the front of `input`, and the bytes after it.

The bytes after it are fewer than the input, which bounds the recursion of a list. -/
def decodeItem (input : List UInt8) :
    Except RlpError (Item × { rest : List UInt8 // rest.length < input.length }) :=
  match input with
  -- There is no first byte.
  | [] => .error (.inputTooShort 1 0)
  | first :: tail =>
    -- A byte below `0x80` is its own encoding.
    if first < 0x80 then
      .ok (.bytes ⟨#[first]⟩, ⟨tail, by simp⟩)
    else do
      let (kind, k, length) ← readPrefix first tail
      -- The payload starts after the `k` bytes of its length.
      let body := tail.drop k
      -- The payload must fit in what is left of the input.
      if length ≤ body.length then
        let payload := body.take length
        let rest : { rest : List UInt8 // rest.length < (first :: tail).length } :=
          ⟨body.drop length, by simp [body]; omega⟩
        match kind with
        | .bytes =>
          match payload with
          -- One byte below `0x80` is its own encoding, never `0x81` then the byte.
          | [byte] =>
            if byte < 0x80 then .error (.singleByteWithPrefix byte)
            else .ok (.bytes ⟨#[byte]⟩, rest)
          | _ => .ok (.bytes ⟨payload.toArray⟩, rest)
        | .list =>
          -- The payload of a list is its items, one after another, with nothing left over.
          let items ← decodeItems payload
          .ok (.list items, rest)
      else
        .error (.inputTooShort length body.length)
termination_by 2 * input.length
decreasing_by simp; omega

/-- The items whose encodings, one after another, are exactly `payload`. -/
def decodeItems (payload : List UInt8) : Except RlpError (List Item) :=
  if payload.isEmpty then
    .ok []
  else do
    -- The first item, then the items of what is left.
    let (item, ⟨rest, _⟩) ← decodeItem payload
    let items ← decodeItems rest
    .ok (item :: items)
termination_by 2 * payload.length + 1

end

/-- The item that `input` encodes.

It fails unless `input` is exactly the encoding of one item. -/
def decode (input : ByteArray) : Except RlpError Item := do
  let (item, ⟨rest, _⟩) ← decodeItem input.data.toList
  -- The encoding of the item must be the whole input.
  if rest.isEmpty then
    .ok item
  else
    .error (.trailingBytes rest.length)

end EthLib.Serialization.Rlp
