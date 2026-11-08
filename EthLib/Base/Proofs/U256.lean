module

public import EthLib.Base.U256
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: `U256`

The two's complement reading of a word is the signed value of its bit vector.

On `[-2^255, 2^255)`, that reading inverts the encoding of an integer.

A word and its 32 big-endian bytes determine each other.
-/

@[expose] public section

namespace EthLib.Base.U256

/-- The two's complement reading is the signed value of the bit vector. -/
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

/-- The 32 bytes of a word are its big-endian value. -/
theorem toList_toBeBytes (w : U256) : (toBeBytes w).toList = natToBytes 32 w.toNat := by
  simp [toBeBytes]

/-- Reading back the 32 bytes of a word gives the word. -/
theorem fromBeBytes_toBeBytes (w : U256) : fromBeBytes (toBeBytes w) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_fromBeBytes, toList_toBeBytes]
  exact bytesToNat_natToBytes_of_lt w.isLt

/-- Writing back the word of 32 bytes gives the same bytes. -/
theorem toBeBytes_fromBeBytes (bytes : Vector UInt8 32) :
    toBeBytes (fromBeBytes bytes) = bytes := by
  apply Vector.toList_inj.mp
  rw [toList_toBeBytes, natToBytes_toNat_fromBeBytes]

/-- Two words with the same bytes are the same word. -/
theorem toBeBytes_inj {a b : U256} (h : toBeBytes a = toBeBytes b) : a = b := by
  rw [← fromBeBytes_toBeBytes a, h, fromBeBytes_toBeBytes]

end EthLib.Base.U256
