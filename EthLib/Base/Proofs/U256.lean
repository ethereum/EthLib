module

public import EthLib.Base.U256

/-!
# Proofs: `U256`

The two's complement reading of a word is Lean's `BitVec.toInt`, and it inverts `fromSigned` on `[-2^255, 2^255)`.
-/

@[expose] public section

namespace EthLib.Base.U256

/-- `to_signed` agrees with `BitVec.toInt`. -/
theorem toSigned_eq_toInt (w : U256) : toSigned w = w.toInt := by
  unfold toSigned
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

/-- Every word is the encoding of its signed reading. -/
theorem fromSigned_toSigned (w : U256) : fromSigned (toSigned w) = w := by
  rw [toSigned_eq_toInt, fromSigned, BitVec.ofInt_toInt]

/-- On `[-2^255, 2^255)`, reading back an encoded integer gives the integer. -/
theorem toSigned_fromSigned {v : Int} (hlo : -2 ^ 255 ≤ v) (hhi : v < 2 ^ 255) : toSigned (fromSigned v) = v := by
  rw [toSigned_eq_toInt, fromSigned, BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

end EthLib.Base.U256
