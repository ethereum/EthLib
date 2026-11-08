module

public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Cryptography.Proofs.Secp256k1.Ecdh
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery

/-!
# Proofs: Ethereum addresses

- The 64 hashed bytes are the uncompressed SEC 1 encoding without its `04` prefix.
- Every private key in `[1, n - 1]` has an address, and only the key `0` has none.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Point

/-- The 64 bytes of `ECDSAPUBKEY` follow the prefix `04` in the uncompressed encoding. -/
theorem encodeUncompressed_eq (x y : Fp) :
    (affine x y).encodeUncompressed = ⟨#[0x04]⟩ ++ publicKeyBytes x y := by
  simp only [encodeUncompressed, publicKeyBytes]
  apply ByteArray.ext
  simp

/-- Every private key in `[1, n - 1]` has an address: `d G` is not `O`. -/
theorem addressOfPrivateKey_ne_none {d : Fn} (hd : d ≠ 0) : addressOfPrivateKey d ≠ none := by
  unfold addressOfPrivateKey
  have h := Ecdsa.mul_generator_ne_infinity hd
  split
  · rename_i heq
    exact absurd heq h
  · simp

/-- A private key has no address exactly when it is zero. -/
theorem addressOfPrivateKey_eq_none_iff {d : Fn} : addressOfPrivateKey d = none ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    exact addressOfPrivateKey_ne_none hd h
  · rintro rfl
    unfold addressOfPrivateKey
    rw [mul_zero_left isOnCurve_generator]

end EthLib.Cryptography.Secp256k1
