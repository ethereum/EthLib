module

public import EthLib.Base.Proofs.ByteOrder
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Proofs: byte orders as base-256 digits

The bytes of a number are its digits in base 256, and Mathlib lists digits least significant first.

So a little-endian reading is the value of the bytes as digits.

A big-endian reading is the value of the reversed bytes as digits.

Only this module imports Mathlib.

So the other byte-order proofs, and the proofs that use them, stay free of it.
-/

@[expose] public section

namespace EthLib.Base.ByteOrder

/-- A right fold of Horner's rule is the value of the bytes as digits, the lowest first. -/
private theorem foldr_eq_ofDigits (bytes : List UInt8) :
    bytes.foldr (fun b acc => b.toNat + 256 * acc) 0
      = Nat.ofDigits 256 (bytes.map UInt8.toNat) := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp [ih, Nat.ofDigits_cons]

/-- A little-endian reading is the value of the bytes as base-256 digits, the lowest first. -/
theorem ofLE_eq_ofDigits {n : Nat} (v : Vector UInt8 n) :
    ofLE v = Nat.ofDigits 256 (v.toList.map UInt8.toNat) := by
  rw [ofLE_eq_foldr, foldr_eq_ofDigits]

/-- A big-endian reading is the value of the bytes as base-256 digits, the highest first. -/
theorem ofBE_eq_ofDigits (bytes : List UInt8) :
    ofBE bytes = Nat.ofDigits 256 (bytes.reverse.map UInt8.toNat) := by
  -- A left fold is a right fold over the reversed list.
  rw [ofBE_eq_foldl, List.foldl_eq_foldr_reverse, ← foldr_eq_ofDigits]
  simp only [Nat.add_comm]

end EthLib.Base.ByteOrder
