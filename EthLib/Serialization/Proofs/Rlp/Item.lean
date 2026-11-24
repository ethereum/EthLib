module

public import EthLib.Serialization.Rlp.Item
public import EthLib.Base.Proofs.ByteOrder

/-!
# `Serialization.Proofs.Rlp.Item`

The big-endian bytes of the code are `BE` of the Yellow Paper.

The Yellow Paper defines `BE(x)` by two properties of its bytes `b`:

- `b_0` is not zero.
- `x = sum_n b_n * 256^(k - 1 - n)`, where `k` is the number of bytes.

The bytes of the code have both properties, and no other bytes have them.

So `BE` is well defined, and the code computes it.

A bound on the number of bytes keeps the first byte of a prefix below 256.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- The bytes of `BE(n)` are `n` in base 256 on as few bytes as it needs. -/
theorem bigEndian_data_toList (n : Nat) :
    (bigEndian n).data.toList
      = (Base.ByteOrder.toBE (Base.ByteOrder.byteLength n) n).toList := rfl

/-- `BE(n)` has as many bytes as `n` has digits in base 256. -/
theorem size_bigEndian (n : Nat) : (bigEndian n).size = Base.ByteOrder.byteLength n := by
  simp [bigEndian, ByteArray.size]

/-- `BE(n)` read back in base 256 is `n`. -/
theorem bigEndian_value (n : Nat) : Base.ByteOrder.ofBE (bigEndian n).data.toList = n := by
  rw [bigEndian_data_toList, Base.ByteOrder.ofBE_toBE_byteLength]

/-- `BE(n)` has no leading zero byte. -/
theorem bigEndian_head_ne_zero (n : Nat) : ∀ b ∈ (bigEndian n).data.toList.head?, b ≠ 0 := by
  rw [bigEndian_data_toList]
  exact Base.ByteOrder.head_toBE_byteLength_ne_zero n

/-- A number below `256^k` has at most `k` digits. -/
theorem bigEndian_size_le (n k : Nat) (h : n < 256 ^ k) : (bigEndian n).size ≤ k := by
  rw [size_bigEndian]
  exact Base.ByteOrder.byteLength_le_of_lt h

/-- Bytes with no leading zero are `BE` of the number they write.

So `BE(x)` is the only byte string with the two properties the Yellow Paper asks for. -/
theorem bigEndian_unique (bytes : List UInt8) (h : ∀ b ∈ bytes.head?, b ≠ 0) :
    (bigEndian (Base.ByteOrder.ofBE bytes)).data.toList = bytes := by
  rw [bigEndian_data_toList, Base.ByteOrder.byteLength_ofBE h,
    Base.ByteOrder.toList_toBE_ofBE]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem RlpError.code_injective (e₁ e₂ : RlpError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [RlpError.code] at h; exact absurd h (by decide))

end EthLib.Serialization.Rlp
