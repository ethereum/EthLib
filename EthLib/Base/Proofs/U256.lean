module

public import EthLib.Base.U256
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: `U256`

- The two's complement reading of a word is Lean's `BitVec.toInt`, and it inverts `fromSigned` on `[-2^255, 2^255)`.
- Reading 32 bytes as a word loses nothing: the word is their exact value, and writing it back gives the same bytes.
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

/-- The word of 32 bytes is their big-endian value, with no reduction modulo 2^256. -/
theorem toNat_fromBeBytes (bytes : Vector UInt8 32) :
    (fromBeBytes bytes).toNat = bytesToNat bytes.toList := by
  have h := bytesToNat_lt bytes.toList
  rw [Vector.length_toList] at h
  exact Nat.mod_eq_of_lt h

/-- The 32 big-endian bytes of the word are the bytes it was read from. -/
theorem natToBytes_toNat_fromBeBytes (bytes : Vector UInt8 32) :
    natToBytes 32 (fromBeBytes bytes).toNat = bytes.toList := by
  have h := natToBytes_bytesToNat bytes.toList
  rwa [Vector.length_toList, ← toNat_fromBeBytes] at h

/-- Two buffers of 32 bytes read as the same word only if they are equal. -/
theorem fromBeBytes_injective : Function.Injective fromBeBytes := by
  intro a b h
  apply Vector.toList_inj.mp
  rw [← natToBytes_toNat_fromBeBytes a, ← natToBytes_toNat_fromBeBytes b, h]

end EthLib.Base.U256
