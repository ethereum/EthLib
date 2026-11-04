module

public import EthLib.Base.Address
public import EthLib.Base.Proofs.U256

/-!
# Proofs: `Address`

An address survives the trip through a word.

A word read as an address keeps its value modulo 2^160.

The order on addresses is lawful, as an ordered map needs.
-/

@[expose] public section

namespace EthLib.Base

namespace Address

/-- The word of an address is the big-endian value of its 20 bytes. -/
theorem toNat_toU256 (a : Address) : a.toU256.toNat = bytesToNat a.toList := by
  have h := bytesToNat_lt a.toList
  rw [Vector.length_toList] at h
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

end Address

/-- The masked address is the word written on 20 bytes. -/
theorem toList_toAddressMasked (w : U256) :
    (toAddressMasked w).toList = natToBytes 20 w.toNat := by
  rw [toAddressMasked, Vector.toList_drop, U256.toList_toBeBytes]
  -- The 32 bytes are 12 high bytes, then the word written on 20 bytes.
  rw [show 32 = 12 + 20 from rfl, natToBytes_add]
  exact List.drop_left' (natToBytes_length _ _)

/-- Masking the word of an address gives the address back. -/
theorem toAddressMasked_toU256 (a : Address) : toAddressMasked a.toU256 = a := by
  apply Vector.toList_inj.mp
  have h := natToBytes_bytesToNat a.toList
  rw [Vector.length_toList] at h
  rw [toList_toAddressMasked, Address.toNat_toU256, h]

/-- The word of a masked address is the word modulo 2^160. -/
theorem toNat_toU256_toAddressMasked (w : U256) :
    (toAddressMasked w).toU256.toNat = w.toNat % 2 ^ 160 := by
  rw [Address.toNat_toU256, toList_toAddressMasked, bytesToNat_natToBytes]

/-- Two addresses with the same word are equal. -/
theorem Address.toU256_injective : Function.Injective Address.toU256 := by
  intro a b h
  rw [← toAddressMasked_toU256 a, ← toAddressMasked_toU256 b, h]

/-! ## The order

Lean core compares two addresses byte by byte, from the first byte.

These checks fail if core stops giving that order the laws an ordered map needs. -/

example : Std.TransOrd Address := inferInstance

example : Std.LawfulEqOrd Address := inferInstance

end EthLib.Base
