import EthLib.Serialization.Rlp.Scalar
import EthLib.Serialization.Proofs.Rlp.Canonical
import EthLib.Serialization.Proofs.Rlp.Bound
import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# `Serialization.Proofs.Rlp.Scalar`

The decoding of a scalar is the inverse of its encoding, and accepts only canonical input.

- `toScalar_scalar`: the item of a scalar holds that scalar.
- `eq_scalar_of_toScalar`: an item that holds a scalar is the item of that scalar.
- `decodeScalar_eq_ok_iff`: `decodeScalar b = .ok n` exactly when `b` is the encoding of `n`.
- `encode_scalar_succeeds`: every scalar below `2^256` has an encoding, so every 256-bit word does.
-/

namespace EthLib.Serialization.Rlp

/-- The item of a scalar holds that scalar. -/
theorem toScalar_scalar (n : Nat) : (Item.scalar n).toScalar = .ok n := by
  -- `BE(n)` has no leading zero byte, and reads back as `n`.
  have hHead : (bigEndian n).data.toList.head? ≠ some 0 := fun h0 =>
    bigEndian_head_ne_zero n 0 h0 rfl
  simp [Item.scalar, Item.toScalar, hHead, bigEndian_value]

/-- An item that holds a scalar is the item of that scalar. -/
theorem eq_scalar_of_toScalar (x : Item) (n : Nat) (h : x.toScalar = .ok n) : x = .scalar n := by
  match x with
  | .bytes data =>
    simp only [Item.toScalar] at h
    by_cases hZero : data.data.toList.head? = some 0
    · simp [hZero] at h
    · simp only [hZero, ite_false, Except.ok.injEq] at h
      subst h
      -- Bytes with no leading zero are `BE` of the number they write.
      have hUnique := bigEndian_unique data.data.toList (fun b hb hb0 => by subst hb0; exact hZero hb)
      simp only [Item.scalar, Item.bytes.injEq]
      exact (byteArray_eq_of_toList _ _ hUnique).symm
  | .list _ => simp [Item.toScalar] at h

/-- Two scalars with the same item are equal. -/
theorem scalar_injective (m n : Nat) (h : Item.scalar m = Item.scalar n) : m = n := by
  have := toScalar_scalar m
  rw [h, toScalar_scalar n] at this
  cases this
  rfl

/-- `decodeScalar` decodes exactly the encodings of scalars, and returns the scalar encoded. -/
theorem decodeScalar_eq_ok_iff (b : ByteArray) (n : Nat) :
    decodeScalar b = .ok n ↔ encode (.scalar n) = .ok b := by
  constructor
  · intro h
    unfold decodeScalar at h
    cases hDecode : decode b with
    | error e => simp [hDecode, bind, Except.bind] at h
    | ok x =>
      simp only [hDecode, bind, Except.bind] at h
      -- The item decoded is the item of the scalar, and the input is its encoding.
      rw [← eq_scalar_of_toScalar x n h]
      exact encode_decode b x hDecode
  · intro h
    simp [decodeScalar, decode_encode _ b h, bind, Except.bind, toScalar_scalar]

/-- A scalar whose big-endian bytes number fewer than `2^64` has an encoding. -/
theorem encode_scalar_succeeds_iff (n : Nat) :
    (∃ e, encode (.scalar n) = .ok e) ↔ (bigEndian n).size < 2 ^ 64 :=
  encode_bytes_succeeds_iff (bigEndian n)

/-- Every scalar below `2^256` has an encoding: at most 32 bytes, then a one-byte prefix. -/
theorem encode_scalar_succeeds (n : Nat) (h : n < 2 ^ 256) : ∃ e, encode (.scalar n) = .ok e := by
  have hSize := bigEndian_size_le n 32 (by simpa using h)
  exact (encode_scalar_succeeds_iff n).2 (by omega)

/-! ## Known answers

Each claim pins one input to the scalar it holds, or to the error that rejects it.

`decide +kernel` has the kernel itself evaluate each claim. -/

open Vectors

/-- The error of a failure, or `none` for a success. -/
private def scalarError (result : Except RlpError Nat) : Option RlpError :=
  match result with
  | .error e => some e
  | .ok _ => none

/-- `82 04 00` holds 1024. -/
theorem decodeScalar_1024 : (decodeScalar (byteArrayOf 3 0x820400)).toOption = some 1024 := by
  decide +kernel

/-- `80`, the empty byte string, holds 0. -/
theorem decodeScalar_zero : (decodeScalar (byteArrayOf 1 0x80)).toOption = some 0 := by
  decide +kernel

/-- `00`, the byte string `[00]`, holds no scalar: 0 encodes as `80`. -/
theorem decodeScalar_byte00 : scalarError (decodeScalar (byteArrayOf 1 0x00)) = some .leadingZeroInScalar := by
  decide +kernel

/-- `82 00 01` holds no scalar: 1 encodes as `01`. -/
theorem decodeScalar_leadingZero : scalarError (decodeScalar (byteArrayOf 3 0x820001)) = some .leadingZeroInScalar := by
  decide +kernel

/-- `c0`, the empty list, holds no scalar. -/
theorem decodeScalar_list : scalarError (decodeScalar (byteArrayOf 1 0xc0)) = some .listAsScalar := by
  decide +kernel

end EthLib.Serialization.Rlp
