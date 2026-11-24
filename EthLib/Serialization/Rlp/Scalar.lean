module

public import EthLib.Serialization.Rlp.Decode

/-!
# `Serialization.Rlp.Scalar`

The strict decoding of a scalar, a non-negative integer.

Source: the equation for `RLP(i)` in Appendix B of the Yellow Paper, Shanghai version.

The file is [`Paper.tex` at `efc5f9a`][paper].

[paper]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- The scalar that an item holds: its bytes in base 256, most significant first.

It fails on a list, and on a byte string with a leading zero byte. -/
def Item.toScalar : Item → Except RlpError Nat
  | .bytes data =>
    -- A scalar `i` is encoded as the byte string `BE(i)`.
    --
    -- `BE` writes no leading zero byte, so such bytes are the encoding of no scalar.
    --
    -- The Yellow Paper asks clients to dismiss such data as non-canonical.
    --
    -- For example, `00`, the byte string `[00]`, holds no scalar, since 0 encodes as `80`.
    --
    -- And `82 00 01` holds no scalar, since 1 encodes as `01`.
    if data.data.toList.head? = some 0 then
      .error .leadingZeroInScalar
    -- Otherwise the bytes are `BE(i)` for the scalar `i` that their base-256 sum gives.
    --
    -- For example, `82 04 00` holds 1024.
    --
    -- And `80`, the empty byte string, holds 0.
    else
      -- The big-endian reading inverts `BE` on the byte strings with no leading zero.
      .ok (Base.ByteOrder.ofBE data.data.toList)
  -- `RLP(i) = RLP(BE(i))` is a byte string, never a list.
  | .list _ => .error .listAsScalar

/-- The scalar that `input` encodes.

It fails unless `input` is exactly the encoding of one scalar. -/
def decodeScalar (input : ByteArray) : Except RlpError Nat := do
  -- The item `x` with `RLP(x)` the whole input, then the scalar `i` with `x = BE(i)`.
  let item ← decode input
  item.toScalar

end EthLib.Serialization.Rlp
