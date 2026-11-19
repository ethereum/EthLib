module

public import EthLib.Base.BigEndian
public import EthLib.Base.Bytes

/-!
# ECDSA signatures as bytes

An ECDSA signature over a curve with a 256-bit order is the pair of integers `r` and `s`.

Its byte form here is 64 bytes: `r` then `s`, each as 32 big-endian bytes.

It is the form of the "v4" identity scheme of [EIP-778][eip778], where the recovery id is left out.

[eip778]: https://eips.ethereum.org/EIPS/eip-778
-/

@[expose] public section

namespace EthLib.Cryptography.EcdsaSignature

/-- The length of a signature: `r` then `s`, 32 bytes each. -/
def SIGNATURE_LEN : Nat := 64

/-- The integers `r` and `s` of a signature, each from 32 big-endian bytes, `r` first. -/
def toNats (sig : Vector UInt8 SIGNATURE_LEN) : Nat × Nat :=
  (Base.bytesToNat (sig.toList.take 32), Base.bytesToNat (sig.toList.drop 32))

/-- The integers `r` and `s` of a signature, if the buffer has exactly its length. -/
def read? (bytes : ByteArray) : Option (Nat × Nat) :=
  (Base.exactBytes? SIGNATURE_LEN bytes).map toNats

/-- The integers `r` and `s` of a signature, or the error built from the buffer's other length. -/
def read {ε : Type} (bytes : ByteArray) (bad : Nat → ε) : Except ε (Nat × Nat) :=
  (Base.exactBytes SIGNATURE_LEN bytes bad).map toNats

end EthLib.Cryptography.EcdsaSignature
