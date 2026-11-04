module

/-!
# `Trie.HexPrefix`

The hex-prefix encoding `HP` of a trie path, from Appendix C of the Yellow Paper.

A leaf or an extension node of the trie stores part of a key path, as nibbles.

The first nibble of its encoding holds the node type and the parity of the path length:

- 0: an extension with an even path, followed by a 0 nibble of padding.
- 1: an extension with an odd path, whose first nibble shares the first byte.
- 2: a leaf with an even path, followed by a 0 nibble of padding.
- 3: a leaf with an odd path, whose first nibble shares the first byte.

So the extension path `[1, 2, 3, 4, 5]` encodes as `0x112345`.

The leaf path `[0, f, 1, c, b, 8]` encodes as `0x200f1cb8`.

Every fork since Frontier uses this encoding.

The Yellow Paper defines only the encoding, so the decoder accepts exactly its outputs.
-/

@[expose] public section

namespace EthLib.Execution.Trie

/-- A nibble: half a byte, from 0 to 15. -/
abbrev Nibble := Fin 16

/-- The high nibble of a byte, `(byte & 0xF0) >> 4`. -/
def highNibble (byte : UInt8) : Nibble :=
  ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩

/-- The low nibble of a byte, `byte & 0x0F`. -/
def lowNibble (byte : UInt8) : Nibble :=
  ⟨byte.toNat % 16, by omega⟩

/-- Each byte as its high nibble, then its low nibble.

Source: the function `y` in Appendix D of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex#L1681>. -/
def bytesToNibbleList (bytes : ByteArray) : List Nibble :=
  bytes.data.toList.flatMap fun byte => [highNibble byte, lowNibble byte]

/-- An even number of nibbles, two to a byte, high nibble first.

The bytes are `16 * x[0] + x[1], 16 * x[2] + x[3], ...`. -/
def packNibbles : (x : List Nibble) → x.length % 2 = 0 → List UInt8
  | [], _ => []
  -- One nibble is not an even number of nibbles.
  | [_], h => by simp at h
  | high :: low :: rest, h =>
    -- At most `16 * 15 + 15 = 255`, so the byte holds it.
    UInt8.ofNat (16 * high.val + low.val) :: packNibbles rest (by simp only [List.length_cons] at h; omega)

/-- `HP(x, t)`: the path `x` and the leaf flag `t` as bytes.

Source: Appendix C of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex#L1651>.

`f(t)` is 2 for a leaf and 0 for an extension. -/
def nibbleListToCompact (x : List Nibble) (isLeaf : Bool) : ByteArray :=
  if h : x.length % 2 = 0 then
    -- The first nibble `f(t)` and a 0 nibble of padding make the byte `16 * f(t)`.
    ⟨⟨packNibbles ((if isLeaf then 2 else 0) :: 0 :: x) (by simp only [List.length_cons]; omega)⟩⟩
  else
    -- The first nibble `f(t) + 1` and `x[0]` make the byte `16 * (f(t) + 1) + x[0]`.
    ⟨⟨packNibbles ((if isLeaf then 3 else 1) :: x) (by simp only [List.length_cons]; omega)⟩⟩

/-- Why a byte string is not the hex-prefix encoding of a path. -/
inductive HexPrefixError where
  /-- The input is empty, so it has no first nibble. -/
  | empty
  /-- The first nibble is above 3, which no flag and parity give. -/
  | invalidFirstNibble
  /-- The path is even, and the padding nibble after the first is not 0. -/
  | nonZeroPadding
  deriving Repr, DecidableEq

/-- The path and the leaf flag that `compact` encodes: the inverse of the encoding.

- Bit 0 of the first nibble is the parity of the path length.
- Bit 1 is the leaf flag. -/
def compactToNibbleList (compact : ByteArray) : Except HexPrefixError (List Nibble × Bool) :=
  match bytesToNibbleList compact with
  | firstNibble :: secondNibble :: rest =>
    if 3 < firstNibble.val then
      .error .invalidFirstNibble
    -- An odd path starts at the second nibble, and the leaf flag is a first nibble of 2 or 3.
    else if firstNibble.val % 2 = 1 then
      .ok (secondNibble :: rest, 2 ≤ firstNibble.val)
    -- An even path: the second nibble is padding.
    else if secondNibble = 0 then
      .ok (rest, 2 ≤ firstNibble.val)
    else
      .error .nonZeroPadding
  -- Every byte has two nibbles, so fewer than two nibbles means no byte.
  | _ => .error .empty

end EthLib.Execution.Trie
