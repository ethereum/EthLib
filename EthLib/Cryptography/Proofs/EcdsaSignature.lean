module

public import EthLib.Cryptography.EcdsaSignature

/-!
# Proofs: reading an ECDSA signature

A buffer reads as a signature exactly when it has 64 bytes.

Its first 32 bytes then give `r`, and the rest give `s`.
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

end EthLib.Cryptography.EcdsaSignature
