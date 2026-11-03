module

/-!
# `Trie.HexPrefix`

The hex-prefix encoding `HP` of a trie path, from Appendix C of the Yellow Paper.

A leaf or an extension node of the trie stores part of a key path, as nibbles.

The first nibble of its encoding holds the node type and the parity of the path length:

```text
    first nibble   node        path length
    0              extension   even, then a 0 nibble of padding
    1              extension   odd
    2              leaf        even, then a 0 nibble of padding
    3              leaf        odd

    extension [1, 2, 3, 4, 5]     ->  11 23 45
    leaf      [0, f, 1, c, b, 8]  ->  20 0f 1c b8
```

Every fork from Frontier to Bogota uses it: execution-specs at `2c0c8e7` defines it once, in `merkle_patricia_trie.py`.

The Yellow Paper and execution-specs define only the encoding, so the decoder accepts exactly its outputs.
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

/-- `bytes_to_nibble_list`: each byte as its high nibble, then its low nibble.

Source: Appendix D of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex#L1681).

Executable: [`bytes_to_nibble_list`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/merkle_patricia_trie.py#L395), execution-specs `2c0c8e7`. -/
def bytesToNibbleList (bytes : ByteArray) : List Nibble :=
  bytes.data.toList.flatMap fun byte => [highNibble byte, lowNibble byte]

/-- An even number of nibbles, two to a byte, high nibble first: `16 * x[0] + x[1], 16 * x[2] + x[3], ...`. -/
def packNibbles : (x : List Nibble) → x.length % 2 = 0 → List UInt8
  | [], _ => []
  -- One nibble is not an even number of nibbles.
  | [_], h => by simp at h
  | high :: low :: rest, h =>
    -- At most `16 * 15 + 15 = 255`, so the byte holds it.
    UInt8.ofNat (16 * high.val + low.val) :: packNibbles rest (by simp only [List.length_cons] at h; omega)

/-- `nibble_list_to_compact`: `HP(x, t)`, the path `x` and the leaf flag `t = isLeaf` as bytes.

Source: Appendix C of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex#L1651).

Executable: [`nibble_list_to_compact`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/merkle_patricia_trie.py#L360), execution-specs `2c0c8e7`.

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

/-- The path and the leaf flag that `compact` encodes: the inverse of `nibbleListToCompact`.

- Bit 0 of the first nibble is the parity of the path length.
- Bit 1 is the leaf flag. -/
def compactToNibbleList (compact : ByteArray) : Except HexPrefixError (List Nibble × Bool) :=
  match bytesToNibbleList compact with
  | firstNibble :: secondNibble :: rest =>
    if 3 < firstNibble.val then
      .error .invalidFirstNibble
    -- Bit 1 of a first nibble up to 3 is set exactly when the nibble is at least 2.
    -- An odd path: the second nibble is the first nibble of the path.
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
