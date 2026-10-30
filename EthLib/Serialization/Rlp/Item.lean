/-!
# `Serialization.Rlp.Item`

The values that Recursive Length Prefix (RLP) encodes, and the big-endian bytes of a number.

Source: Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

An item is a byte string or a list of items, so the items form a tree.

For example, `[ "cat", [ "dog" ], [] ]` is a list of three items:

- the byte string `63 61 74`;
- a list that holds the byte string `64 6f 67`;
- the empty list.

The empty byte string and the empty list are different items, with different encodings.
-/

namespace EthLib.Serialization.Rlp

/-- An RLP item: a byte string or a list of items.

The Yellow Paper calls the set of items `T`, its byte strings `B` and its lists `L`. -/
inductive Item where
  /-- A byte string, a leaf of the tree. -/
  | bytes (data : ByteArray)
  /-- A list of items, a branch of the tree. -/
  | list (items : List Item)

/-- Why RLP refused its input. -/
inductive RlpError where
  /-- A payload of `length` bytes, where `length` is `2^64` or more.

  The payload of a byte string is its bytes.

  The payload of a list is the encodings of its items.

  The Yellow Paper gives such an item no encoding. -/
  | payloadTooLong (length : Nat)
  deriving Repr, DecidableEq

/-- `n` in base 256, most significant byte first, using at most `fuel` bytes.

# Why fuel

The recursion counts down a byte budget instead of dividing `n`.

The kernel unfolds such a definition directly, so it can evaluate the known answers.

A budget of `n` bytes never runs out, since `n` has at most `n` digits in base 256.
-/
def bigEndianAux : Nat → Nat → ByteArray
  -- Out of budget: write nothing.
  | _, 0 => .empty
  | n, fuel + 1 =>
      -- No digit is left, and a zero byte here would be a leading zero.
      if n = 0 then
        .empty
      -- The higher digits first, then the lowest one.
      else
        (bigEndianAux (n / 256) fuel).push (UInt8.ofNat (n % 256))

/-- `BE` of the Yellow Paper: `n` in base 256, most significant byte first, with no leading zero byte.

```text
BE(0) = []
BE(127) = [ 7f ]
BE(1024) = [ 04 00 ]
```

`BE(0)` is empty, since the Yellow Paper asks for the shortest such byte string. -/
def bigEndian (n : Nat) : ByteArray :=
  bigEndianAux n n

/-- The number that `bytes` writes in base 256, most significant byte first.

The Yellow Paper defines `BE(x)` as the bytes `b` with `x = sum_n b_n * 256^(k - 1 - n)`, where `k` is their count.

This is that sum, computed one byte at a time. -/
def ofBigEndian (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => 256 * acc + byte.toNat) 0

/-- The item of a scalar `n`: the byte string `BE(n)`.

The Yellow Paper encodes a scalar `i` as `RLP(BE(i))`, so 0 is the empty byte string. -/
def Item.scalar (n : Nat) : Item :=
  .bytes (bigEndian n)

end EthLib.Serialization.Rlp
