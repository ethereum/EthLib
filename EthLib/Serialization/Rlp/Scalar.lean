import EthLib.Serialization.Rlp.Decode

/-!
# `Serialization.Rlp.Scalar`

The strict decoding of a scalar, a non-negative integer.

Source: Appendix B of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex), the equation for `RLP(i)` and the paragraph after it.

A scalar `i` is encoded as the byte string `BE(i)`, which has no leading zero byte.

So a byte string with a leading zero byte holds no scalar, and the Yellow Paper asks clients to reject it.

For example:

- `82 04 00` holds 1024;
- `80`, the empty byte string, holds 0;
- `00`, the byte string `[00]`, holds no scalar, since 0 encodes as `80`;
- `82 00 01` holds no scalar, since 1 encodes as `01`.
-/

namespace EthLib.Serialization.Rlp

/-- The scalar that an item holds: its bytes in base 256, most significant first.

It fails on a list, and on a byte string with a leading zero byte. -/
def Item.toScalar : Item → Except RlpError Nat
  | .bytes data =>
    -- `BE` writes no leading zero byte, so such bytes are the encoding of no scalar.
    if data.data.toList.head? = some 0 then
      .error .leadingZeroInScalar
    else
      .ok (ofBigEndian data.data.toList)
  | .list _ => .error .listAsScalar

/-- The scalar that `input` encodes.

It fails unless `input` is exactly the encoding of one scalar. -/
def decodeScalar (input : ByteArray) : Except RlpError Nat := do
  let item ← decode input
  item.toScalar

end EthLib.Serialization.Rlp
