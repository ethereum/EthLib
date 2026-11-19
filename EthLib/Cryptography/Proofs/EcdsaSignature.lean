module

public import EthLib.Cryptography.EcdsaSignature
import EthLib.Base.Proofs.BigEndian
import EthLib.Base.Proofs.Bytes

/-!
# Proofs: reading and writing an ECDSA signature

A buffer reads as a signature exactly when it has 64 bytes.

Its first 32 bytes then give `r`, and the rest give `s`.

Writing two integers and reading them back gives each one modulo `2^256`.
-/

@[expose] public section

namespace EthLib.Cryptography.EcdsaSignature

/-- A buffer reads as a signature exactly when it has the length of one.

Its first 32 bytes then give `r`, and the rest give `s`. -/
theorem read?_eq (b : ByteArray) :
    read? b = if b.size = SIGNATURE_LEN then
      some (Base.bytesToNat (b.data.toList.take 32), Base.bytesToNat (b.data.toList.drop 32))
    else none := by
  by_cases h : b.size = SIGNATURE_LEN <;> simp [read?, Base.exactBytes?, toNats, h]

/-- The bytes of `r` and `s` read back as `r` and `s`, each modulo `2^256`. -/
@[simp] theorem toNats_toBytes (r s : Nat) :
    toNats (toBytes r s) = (r % 256 ^ 32, s % 256 ^ 32) := by
  have hr := Base.natToBytes_length 32 r
  simp only [toNats, toBytes, Vector.toList_mk, List.take_left' hr,
    List.drop_left' hr, Base.bytesToNat_natToBytes]

/-- The bytes of a signature, as a buffer, read as its two integers. -/
@[simp] theorem read?_packBytes (sig : Vector UInt8 SIGNATURE_LEN) :
    read? (Base.packBytes sig) = some (toNats sig) := by
  simp [read?]

/-- The bytes before the recovery id are the bytes of the signature. -/
@[simp] theorem take_toRecoverableBytes (r s : Nat) (odd : Bool) :
    ((toRecoverableBytes r s odd).take SIGNATURE_LEN : Vector UInt8 SIGNATURE_LEN) =
      toBytes r s := by
  -- The cast that remains is between two forms of the same length.
  simp [toRecoverableBytes, Vector.take_eq_extract]
  rfl

/-- The last byte is the recovery id. -/
@[simp] theorem getElem_toRecoverableBytes (r s : Nat) (odd : Bool) :
    (toRecoverableBytes r s odd)[SIGNATURE_LEN] = if odd then 1 else 0 :=
  Vector.getElem_push_eq

end EthLib.Cryptography.EcdsaSignature
