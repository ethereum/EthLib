module

public import EthLib.Execution.ErrorFormat

/-!
# `Trie.HexPrefix`

The hex-prefix encoding `HP` of a trie path, from Appendix C of the Yellow Paper.

A leaf or an extension node of the trie stores part of a key path, as nibbles.

The first nibble of its encoding holds the node type and the parity of the path length:

- 0: an extension with an even path, followed by a 0 nibble of padding.
- 1: an extension with an odd path, whose first nibble shares the first byte.
- 2: a leaf with an even path, followed by a 0 nibble of padding.
- 3: a leaf with an odd path, whose first nibble shares the first byte.

Every fork since Frontier uses this encoding.
-/

@[expose] public section

namespace EthLib.Execution.Trie

/-- A nibble: half a byte, from 0 to 15. -/
abbrev Nibble := Fin 16

/-- The high nibble of a byte, `floor(byte / 16)`. -/
def highNibble (byte : UInt8) : Nibble :=
  ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩

/-- The low nibble of a byte, `byte mod 16`. -/
def lowNibble (byte : UInt8) : Nibble :=
  ⟨byte.toNat % 16, by omega⟩

/-- Each byte as its high nibble, then its low nibble.

Source: the function `y` in Appendix D of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex#L1681>. -/
def bytesToNibbleList (bytes : ByteArray) : List Nibble :=
  -- `k'[i] = floor(k[i / 2] / 16)` for an even `i`, and `k[floor(i / 2)] mod 16` otherwise.
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
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex#L1651>. -/
def nibbleListToCompact (x : List Nibble) (isLeaf : Bool) : ByteArray :=
  -- `f(t) = 2` if `t ≠ 0`, and `0` otherwise, with `t` the leaf flag.
  if h : x.length % 2 = 0 then
    -- `||x||` even: `(16 * f(t), 16 * x[0] + x[1], 16 * x[2] + x[3], ...)`.
    --
    -- The first nibble `f(t)` and a 0 nibble of padding make the byte `16 * f(t)`.
    --
    -- So the leaf path `[0, f, 1, c, b, 8]` encodes as `0x200f1cb8`.
    ⟨⟨packNibbles ((if isLeaf then 2 else 0) :: 0 :: x) (by simp only [List.length_cons]; omega)⟩⟩
  else
    -- Otherwise: `(16 * (f(t) + 1) + x[0], 16 * x[1] + x[2], 16 * x[3] + x[4], ...)`.
    --
    -- The first nibble `f(t) + 1` and `x[0]` make the byte `16 * (f(t) + 1) + x[0]`.
    --
    -- So the extension path `[1, 2, 3, 4, 5]` encodes as `0x112345`.
    ⟨⟨packNibbles ((if isLeaf then 3 else 1) :: x) (by simp only [List.length_cons]; omega)⟩⟩

/-- Why a byte string is not the hex-prefix encoding of a path. -/
inductive HexPrefixError where
  /-- The input is empty, so it has no first nibble. -/
  | empty
  /-- The first nibble `nibble` is above 3, which no flag and parity give. -/
  | invalidFirstNibble (nibble : Nat)
  /-- The path is even, and the padding nibble `nibble` after the first is not 0. -/
  | nonZeroPadding (nibble : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def hexPrefixErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Trie.HexPrefixError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named. -/
def HexPrefixError.reprPrec : HexPrefixError → Nat → Std.Format
  | .empty, p => hexPrefixErrorFormat "empty" [] p
  | .invalidFirstNibble nibble, p =>
    hexPrefixErrorFormat "invalidFirstNibble" [namedArg "nibble" nibble] p
  | .nonZeroPadding nibble, p => hexPrefixErrorFormat "nonZeroPadding" [namedArg "nibble" nibble] p

instance : Repr HexPrefixError := ⟨HexPrefixError.reprPrec⟩

/-- The path and the leaf flag that `compact` encodes: the inverse of the encoding.

The Yellow Paper defines only the encoding, so the decoder accepts exactly its outputs.

- Bit 0 of the first nibble is the parity of the path length.
- Bit 1 is the leaf flag. -/
def compactToNibbleList (compact : ByteArray) : Except HexPrefixError (List Nibble × Bool) :=
  match bytesToNibbleList compact with
  | firstNibble :: secondNibble :: rest =>
    -- The first nibble is `f(t)` or `f(t) + 1`, so at most 3.
    if 3 < firstNibble.val then
      .error (.invalidFirstNibble firstNibble.val)
    -- An odd path starts at the second nibble, and the leaf flag is a first nibble of 2 or 3.
    else if firstNibble.val % 2 = 1 then
      .ok (secondNibble :: rest, 2 ≤ firstNibble.val)
    -- An even path: the second nibble is padding.
    else if secondNibble = 0 then
      .ok (rest, 2 ≤ firstNibble.val)
    else
      .error (.nonZeroPadding secondNibble.val)
  -- Every byte has two nibbles, so fewer than two nibbles means no byte.
  | _ => .error .empty

end EthLib.Execution.Trie
