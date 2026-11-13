module

public import EthLib.Serialization.Rlp.Encode

/-!
# `Serialization.Rlp.Decode`

The strict RLP decoding: the inverse of the encoding, which rejects every other input.

Source: Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`][paper].

The Yellow Paper defines only the encoding.

So the decoder accepts exactly the outputs of the encoding, and nothing else.

Every item has one encoding, so two decoders that follow this rule agree on every input.

A lax decoder would accept bytes that the encoding never writes.

There are three such forms, each longer than the real encoding:

- A byte below `0x80` written with a prefix, as `81 05` for `05`.
- A length below 56 written in the long form, as `b8 03` for `83`.
- A length written with a leading zero byte, as `b9 00 40` for `b8 40`.

The decoder rejects all three, and any input that ends early or has bytes left after the item.

[paper]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- The number that the `k` bytes of `input` from `pos` write in base 256, after the value `acc`.

Each byte multiplies the value so far by 256, then adds itself. -/
def readBigEndian (input : ByteArray) (pos k acc : Nat)
    (inside : pos + k ≤ input.size := by omega) : Nat :=
  match k with
  | 0 => acc
  | k + 1 => readBigEndian input (pos + 1) k
      (256 * acc + (input[pos]'(by omega)).toNat) (by omega)

/-- What the first bytes of an encoding announce, from its first byte `first`.

The bytes of `input` from `pos` to `stop` follow the first byte.

The result is the kind of payload, the number `k` of bytes that write the length, and the length.

- From `0x80` to `0xb7`, a byte string of `first - 0x80` bytes, and `k = 0`.
- From `0xb8` to `0xbf`, a byte string whose length is on the next `k = first - 0xb7` bytes.
- From `0xc0` to `0xf7`, a list payload of `first - 0xc0` bytes, and `k = 0`.
- From `0xf8` to `0xff`, a list payload whose length is on the next `k = first - 0xf7` bytes.

A byte below `0x80` is its own encoding and announces nothing, so it is not passed here. -/
def readPrefix (input : ByteArray) (first : UInt8) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) :
    Except RlpError (PayloadKind × Nat × Nat) :=
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
  readLongLength (kind : PayloadKind) (k : Nat) :
      Except RlpError (PayloadKind × Nat × Nat) :=
    -- The `k` bytes of the length must all be there.
    if short : stop - pos < k then
      .error (.inputTooShort k (stop - pos))
    -- No length bytes would write a length of zero, which takes the short form.
    else if zero : k = 0 then
      .error (.longFormForShortLength 0)
    -- `BE` has no leading zero byte, and `k` is at least 1 here.
    else if input[pos]'(by omega) = 0 then
      .error .leadingZeroInLength
    else
      let length := readBigEndian input pos k 0 (by omega)
      -- A length below 56 fits in the first byte, so its long form is never written.
      if length < 56 then
        .error (.longFormForShortLength length)
      else
        .ok (kind, k, length)

mutual

/-- One item read from the bytes of `input` from `pos` to `stop`, and the position after it.

That position is past `pos`, which bounds the recursion of a list.

The decoder reads the bytes in place, and copies only the bytes of each byte string.

The bound on the end position keeps every byte read inside `input`. -/
def decodeItem (input : ByteArray) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) :
    Except RlpError (Item × { next : Nat // pos < next ∧ next ≤ stop }) :=
  -- There is no first byte.
  if hPos : pos < stop then
    let first := input[pos]'(by omega)
    -- A byte below `0x80` is its own encoding.
    if first < 0x80 then
      .ok (.bytes ⟨#[first]⟩, ⟨pos + 1, by omega, by omega⟩)
    else do
      let (kind, k, length) ← readPrefix input first (pos + 1) stop
      -- The payload starts after the `k` bytes of its length.
      let start := pos + 1 + k
      -- The payload must fit in what is left of the input.
      if hFit : start + length ≤ stop then
        let next : { next : Nat // pos < next ∧ next ≤ stop } := ⟨start + length, by omega, hFit⟩
        match kind with
        | .bytes =>
          -- One byte below `0x80` is its own encoding, never `0x81` then the byte.
          if low : length = 1 ∧ ∃ inside : start < input.size, input[start] < 0x80 then
            .error (.singleByteWithPrefix (input[start]'low.2.1))
          else
            .ok (.bytes (input.extract start (start + length)), next)
        | .list =>
          -- The payload of a list is its items, one after another, with nothing left over.
          let items ← decodeItems input start (start + length)
          .ok (.list items, next)
      else
        .error (.inputTooShort length (stop - start))
  else
    .error (.inputTooShort 1 0)
termination_by 3 * (stop - pos)
decreasing_by omega

/-- The items whose encodings, one after another, are exactly the bytes from `pos` to `stop`. -/
def decodeItems (input : ByteArray) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) : Except RlpError (List Item) :=
  decodeItemsFrom input pos stop []
termination_by 3 * (stop - pos) + 2

/-- The items read so far, in reverse order, then the items from `pos` to `stop`.

The loop runs in constant stack for any number of items. -/
def decodeItemsFrom (input : ByteArray) (pos stop : Nat) (done : List Item)
    (bounded : stop ≤ input.size := by omega) :
    Except RlpError (List Item) :=
  if pos < stop then do
    -- The first item, then the items of what is left.
    let (item, ⟨next, _⟩) ← decodeItem input pos stop
    decodeItemsFrom input next stop (item :: done)
  else
    .ok done.reverse
termination_by 3 * (stop - pos) + 1

end

/-- The item that `input` encodes.

It fails unless `input` is exactly the encoding of one item. -/
def decode (input : ByteArray) : Except RlpError Item := do
  let (item, ⟨next, _⟩) ← decodeItem input 0 input.size
  -- The encoding of the item must be the whole input.
  if next = input.size then
    .ok item
  else
    .error (.trailingBytes (input.size - next))

end EthLib.Serialization.Rlp
