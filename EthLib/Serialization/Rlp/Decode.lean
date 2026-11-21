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

/-- The head of an item at `pos`, read inside the bytes up to `stop`.

A byte string is read whole, and a list gives the bounds of its payload. -/
inductive ItemHead (pos stop : Nat) where
  /-- A byte string, and the position after it. -/
  | bytes (value : ByteArray) (next : Nat) (after : pos < next) (within : next ≤ stop)
  /-- A list whose payload runs from `start` to `next`, the position after the list. -/
  | list (start next : Nat) (after : pos < start) (ordered : start ≤ next) (within : next ≤ stop)

/-- The head of the item of `input` at `pos`, read inside the bytes up to `stop`.

It checks every rule of an item except those on the items of a list, which come later. -/
def readHead (input : ByteArray) (pos stop : Nat) (bounded : stop ≤ input.size := by omega) :
    Except RlpError (ItemHead pos stop) :=
  -- There is no first byte.
  if hPos : pos < stop then
    let first := input[pos]'(by omega)
    -- A byte below `0x80` is its own encoding.
    if first < 0x80 then
      .ok (.bytes ⟨#[first]⟩ (pos + 1) (by omega) (by omega))
    else do
      let (kind, k, length) ← readPrefix input first (pos + 1) stop
      -- The payload starts after the `k` bytes of its length.
      let start := pos + 1 + k
      -- The payload must fit in what is left of the input.
      if hFit : start + length ≤ stop then
        match kind with
        | .bytes =>
          -- One byte below `0x80` is its own encoding, never `0x81` then the byte.
          if low : length = 1 ∧ ∃ inside : start < input.size, input[start] < 0x80 then
            .error (.singleByteWithPrefix (input[start]'low.2.1))
          else
            .ok (.bytes (input.extract start (start + length)) (start + length) (by omega) hFit)
        | .list => .ok (.list start (start + length) (by omega) (by omega) hFit)
      else
        .error (.inputTooShort length (stop - start))
  else
    .error (.inputTooShort 1 0)

/-- A list that the decoder has opened: the end of its payload, and its items so far, last first. -/
structure OpenList (size : Nat) where
  /-- The position where the payload of the list ends. -/
  stop : Nat
  /-- The payload ends inside the input. -/
  bounded : stop ≤ size
  /-- The items read so far, in reverse order. -/
  done : List Item

/-- The items from `pos` to the end of the list `current`, inside the lists of `outer`.

Each list of `outer` holds the one before it, and the last holds the items asked for.

A nested list opens on top of `current`, and returns to it when its payload ends.

So the loop runs in constant native stack, whatever the depth of the nesting. -/
def decodeItemsLoop (input : ByteArray) (pos : Nat) (current : OpenList input.size)
    (outer : List (OpenList input.size)) : Except RlpError (List Item) :=
  if hPos : pos < current.stop then
    match readHead input pos current.stop current.bounded with
    | .error e => .error e
    | .ok (.bytes value next after within) =>
      decodeItemsLoop input next { current with done := .bytes value :: current.done } outer
    | .ok (.list start next after ordered within) =>
      decodeItemsLoop input start ⟨next, by have := current.bounded; omega, []⟩ (current :: outer)
  else
    -- The payload of `current` ends at `pos`, so the list is whole.
    match outer with
    | [] => .ok current.done.reverse
    | parent :: rest =>
      decodeItemsLoop input pos
        { parent with done := .list current.done.reverse :: parent.done } rest
termination_by (input.size - pos, outer.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; have := current.bounded; omega)
    | (apply Prod.Lex.right; simp)

/-- The items read so far, in reverse order, then the items from `pos` to `stop`. -/
def decodeItemsFrom (input : ByteArray) (pos stop : Nat) (done : List Item)
    (bounded : stop ≤ input.size := by omega) : Except RlpError (List Item) :=
  decodeItemsLoop input pos ⟨stop, bounded, done⟩ []

/-- The items whose encodings, one after another, are exactly the bytes from `pos` to `stop`. -/
def decodeItems (input : ByteArray) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) : Except RlpError (List Item) :=
  decodeItemsFrom input pos stop []

/-- One item read from the bytes of `input` from `pos` to `stop`, and the position after it.

That position is past `pos`.

The decoder reads the bytes in place, and copies only the bytes of each byte string.

The bound on the end position keeps every byte read inside `input`. -/
def decodeItem (input : ByteArray) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) :
    Except RlpError (Item × { next : Nat // pos < next ∧ next ≤ stop }) :=
  match readHead input pos stop bounded with
  | .error e => .error e
  | .ok (.bytes value next after within) => .ok (.bytes value, ⟨next, after, within⟩)
  | .ok (.list start next after ordered within) =>
    -- The payload of a list is its items, one after another, with nothing left over.
    match decodeItems input start next with
    | .error e => .error e
    | .ok items => .ok (.list items, ⟨next, by omega, within⟩)

/-- The item that `input` encodes.

It fails unless `input` is exactly the encoding of one item. -/
def decode (input : ByteArray) : Except RlpError Item := do
  let (item, ⟨next, _⟩) ← decodeItem input 0 input.size
  -- The encoding of the item must be the whole input.
  if next = input.size then
    .ok item
  else
    .error (.trailingBytes (input.size - next))

/-- An item, and the bytes of its encoding that a decoder read it from.

A caller that keeps these bytes can hash the item without encoding it again.

The structure does not check that the bytes encode the item.

The decoder of messages proves it for what it reads. -/
structure Encoded where
  /-- The item. -/
  item : Item
  /-- The bytes that the item was read from. -/
  bytes : ByteArray
  deriving DecidableEq

/-- The encodings so far, then those of the items one after another from `pos` to `stop`.

Each encoding is found from the head of its item alone, without reading inside a list.

So a nested list costs one step, whatever its depth. -/
def splitItems (input : ByteArray) (pos stop : Nat) (bounded : stop ≤ input.size)
    (done : Array ByteArray) : Except RlpError (Array ByteArray) :=
  if pos < stop then
    match readHead input pos stop bounded with
    | .error e => .error e
    | .ok (.bytes _ next _ _) =>
      splitItems input next stop bounded (done.push (input.extract pos next))
    | .ok (.list _ next _ _ _) =>
      splitItems input next stop bounded (done.push (input.extract pos next))
  else
    .ok done
termination_by stop - pos

/-- The encodings of the items of the list that `input` encodes, one for each item, in order.

Only the head of each item is read, so the items themselves are not checked. -/
def listEncodings (input : ByteArray) : Except RlpError (List ByteArray) :=
  match readHead input 0 input.size with
  | .error e => .error e
  | .ok (.bytes ..) => .error .bytesAsList
  | .ok (.list start next _ _ within) =>
    if next = input.size then (splitItems input start next within #[]).map (·.toList)
    else .error (.trailingBytes (input.size - next))

/-- Each item next to its encoding, in order.

It fails when there are not as many encodings as items. -/
def Encoded.zip (items : List Item) (encodings : List ByteArray) :
    Except RlpError (List Encoded) :=
  if items.length = encodings.length then .ok (List.zipWith Encoded.mk items encodings)
  else .error (.wrongFieldCount items.length encodings.length)

/-- The items of a list, each with its slice of the bytes of the list.

A byte string has no items. -/
def Encoded.parts (e : Encoded) : Except RlpError (List Encoded) :=
  match e.item with
  | .list items => listEncodings e.bytes >>= Encoded.zip items
  | .bytes _ => .error .bytesAsList

/-- The encodings of the items of the payload of the envelope that `data` encodes.

The envelope is `[request-id, payload]`, and the payload is a list. -/
def payloadEncodings (data : ByteArray) : Except RlpError (List ByteArray) := do
  match ← listEncodings data with
  | [_, payload] => listEncodings payload
  | encodings => throw (.wrongFieldCount 2 encodings.length)

end EthLib.Serialization.Rlp
