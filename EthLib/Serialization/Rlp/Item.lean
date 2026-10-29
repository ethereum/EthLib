/-!
# `Serialization.Rlp.Item`

The values that Recursive Length Prefix (RLP) encodes.

RLP is the serialization of the execution layer.

Block headers, transactions, receipts and trie nodes are written with it.

Appendix B of the Yellow Paper (Shanghai version, `ethereum/yellowpaper` at `efc5f9a`) defines it.

An item is a byte string or a list of items, so the items form a tree:

```text
    [ "cat", [ "dog" ], [] ]

    list
     |- byte string  63 61 74
     |- list
     |   '- byte string  64 6f 67
     '- list, empty
```

The empty byte string and the empty list are different items, with different encodings.

A scalar, a non-negative integer, is encoded as a byte string: its digits in base 256, with no leading zero.
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
  /-- A byte string or a list whose payload has `length` bytes, where `length` is `2^64` or more.

  The payload of a byte string is its bytes, and the payload of a list is the encodings of its items.

  The Yellow Paper gives such an item no encoding. -/
  | payloadTooLong (length : Nat)
  deriving Repr, DecidableEq

/-- `n` in base 256, most significant byte first, using at most `fuel` bytes.

# Why fuel

The recursion counts down a byte budget instead of shrinking `n`.

The kernel unfolds such a definition directly, so it can evaluate the known answers.

`bigEndian` passes a budget of `n`, which never runs out: `n` has at most `n` digits in base 256.
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
    BE(0)     =  []
    BE(127)   =  [ 7f ]
    BE(1024)  =  [ 04 00 ]
```

`BE(0)` is empty, since the Yellow Paper asks for a byte array of minimal length.
-/
def bigEndian (n : Nat) : ByteArray :=
  bigEndianAux n n

/-- The item of a scalar `n`: the byte string `BE(n)`.

The Yellow Paper encodes a scalar `i` as `RLP(BE(i))`.

So 0 is the empty byte string. -/
def Item.scalar (n : Nat) : Item :=
  .bytes (bigEndian n)

end EthLib.Serialization.Rlp
