module

public import EthLib.Serialization.Rlp.Item

/-!
# `Serialization.Rlp.Encode`

The RLP encoding of an item.

Source: `R_b`, `R_l` and `s` in Appendix B of the Yellow Paper, Shanghai version.

The file is [`Paper.tex` at `efc5f9a`][paper].

An encoding is a prefix, then a payload.

The payload of a byte string is its bytes.

The payload of a list is the encodings of its items, one after another.

A single byte below `0x80` is the one exception: it is its own encoding, with no prefix.

For example, the list of the byte strings `cat` and `dog` encodes as `c8 83 63 61 74 83 64 6f 67`.

Its prefix `c8` is `0xc0 + 8`, and each byte string is the prefix `83 = 0x80 + 3`, then 3 bytes.

A payload of `2^64` bytes or more has no encoding.

[paper]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- What a payload holds: the bytes of a byte string, or the encodings of the items of a list. -/
inductive PayloadKind where
  /-- The bytes of a byte string. -/
  | bytes
  /-- The encodings of the items of a list. -/
  | list

/-- The prefix byte of an empty payload: `0x80` for a byte string, `0xc0` for a list. -/
def PayloadKind.offset : PayloadKind → Nat
  -- 128 in `R_b`.
  | .bytes => 0x80
  -- 192 in `R_l`.
  | .list => 0xc0

/-- The prefix that `R_b` or `R_l` writes before a payload of `length` bytes.

It fails from `2^64` bytes on. -/
def lengthPrefix (kind : PayloadKind) (length : Nat) : Except RlpError ByteArray :=
  -- `R_b` case 2 and `R_l` case 1, below 56: the one byte `128 + ||x||` or `192 + ||s(x)||`.
  if length < 56 then
    .ok ⟨#[UInt8.ofNat (kind.offset + length)]⟩
  -- `R_b` case 3, below `2^64`: `(183 + ||BE(||x||)||) · BE(||x||)`.
  --
  -- `R_l` case 2 is the same, with 247 and `||s(x)||` for 183 and `||x||`.
  --
  -- The Yellow Paper's 183 and 247 are the offsets 128 and 192 plus 55.
  else if length < 2 ^ 64 then
    -- Below `2^64`, `BE(length)` has at most 8 bytes.
    --
    -- So the first byte of a byte string is at most `183 + 8 = 191`, below 192, where lists start.
    --
    -- And the first byte of a list is at most `247 + 8 = 255`, which is still a byte.
    let lengthBytes := bigEndian length
    .ok (⟨#[UInt8.ofNat (kind.offset + 55 + lengthBytes.size)]⟩ ++ lengthBytes)
  -- The last case of `R_b` and of `R_l`: from `2^64` bytes on, `∅`, no encoding.
  else
    .error (.payloadTooLong length)

/-- Whether `data` is a single byte below `0x80`: then it is its own encoding. -/
def isSingleLowByte (data : ByteArray) : Bool :=
  -- The condition of `R_b` case 1: `||x|| = 1` and `x[0] < 128`.
  if h : data.size = 1 then decide (data[0] < 0x80) else false

/-- `R_b` of the Yellow Paper: the encoding of a byte string. -/
def encodeBytes (data : ByteArray) : Except RlpError ByteArray :=
  -- `R_b` case 1: `x` itself, if `||x|| = 1` and `x[0] < 128`.
  if isSingleLowByte data then
    .ok data
  -- `R_b` cases 2 to 4: the prefix of `||x||`, then `x`, or no encoding.
  else do
    return (← lengthPrefix .bytes data.size) ++ data

mutual

/-- `RLP` of the Yellow Paper: the encoding of an item.

It fails only when a payload has `2^64` bytes or more. -/
def encode : Item → Except RlpError ByteArray
  -- `RLP(x) = R_b(x)` for `x` in `B`.
  | .bytes data => encodeBytes data
  -- `RLP(x) = R_l(x)` otherwise: the prefix of `||s(x)||`, then `s(x)`.
  --
  -- `R_l` gives no encoding when `s(x)` has none, so a failure of the payload stops here.
  --
  -- EthLib reads the `∅` of the guard `s(x) ≠ ∅` as no encoding, as the last case of `s` writes it.
  --
  -- The empty list has `s(x) = ()`, the empty sequence, so it encodes as `c0`.
  --
  -- The paper also writes `∅` for an empty value elsewhere, so this reading is EthLib's choice.
  | .list items => do
      let payload ← joinEncodings items
      return (← lengthPrefix .list payload.size) ++ payload
  -- Structural recursion, which the kernel unfolds to evaluate the known answers.
  termination_by structural item => item

/-- `s` of the Yellow Paper: the encodings of `items`, one after another.

It fails when the encoding of one of them fails. -/
def joinEncodings : List Item → Except RlpError ByteArray
  -- The empty concatenation, for the empty list.
  | [] => .ok .empty
  -- `s(x) = RLP(x[0]) · RLP(x[1]) · ...`, and no encoding if one `RLP(x[i])` has none.
  | item :: rest => do
      let head ← encode item
      joinEncodingsFrom rest head
  termination_by structural items => items

/-- The encodings so far, then the encodings of `items`, one after another.

Each encoding is appended in place, and the loop runs in constant stack for any length. -/
def joinEncodingsFrom : List Item → ByteArray → Except RlpError ByteArray
  | [], out => .ok out
  -- The next factor `RLP(x[i])` of `s(x)`, appended to the bytes so far.
  --
  -- A failure of any of them is a failure of `s(x)`.
  | item :: rest, out => do
      let head ← encode item
      joinEncodingsFrom rest (out ++ head)
  termination_by structural items => items

end

end EthLib.Serialization.Rlp
