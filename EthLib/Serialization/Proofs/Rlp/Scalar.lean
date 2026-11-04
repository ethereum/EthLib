module

public import EthLib.Serialization.Rlp.Scalar
public import EthLib.Serialization.Proofs.Rlp.Canonical
public import EthLib.Serialization.Proofs.Rlp.Bound

/-!
# `Serialization.Proofs.Rlp.Scalar`

The decoding of a scalar is the inverse of its encoding, and accepts only canonical input.

The item of a scalar holds that scalar, and an item that holds a scalar is its item.

The bytes `b` decode to the scalar `n` exactly when `b` is the encoding of `n`.

Every scalar below `2^256` has an encoding, so every 256-bit word does.
-/

@[expose] public section

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

/-- The scalar decoder accepts exactly the encodings of scalars, and returns the scalar. -/
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

end EthLib.Serialization.Rlp
