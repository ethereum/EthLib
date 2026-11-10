module

public import EthLib.Cryptography.Proofs.Hash.Hkdf
public import EthLib.Networking.Noise

/-!
# Proofs: Noise XX

[Noise revision 34, §4.3](https://noiseprotocol.org/noise_rev34.pdf) computes two outputs from HMAC.

Its note calls this function HKDF of [RFC 5869](https://www.rfc-editor.org/rfc/rfc5869#section-2).

There the chaining key is the salt, and the info is empty.

So the two outputs are the first 64 bytes of that HKDF.

Distinct kinds of handshake error have distinct codes.
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Base
open EthLib.Cryptography.Hash

/-- The two outputs are the first 64 bytes of HKDF, with the chaining key as salt and empty info. -/
theorem hkdf_eq_hkdf2 (chainingKey : Key) (input : ByteArray) :
    Hkdf.hkdf (packBytes chainingKey) input .empty 64 =
      .ok (packBytes (hkdf2 chainingKey input).1 ++ packBytes (hkdf2 chainingKey input).2) := by
  have hprk : Hkdf.HASH_LEN ≤ (Hkdf.extract (packBytes chainingKey) input).size := by
    simp [Hkdf.extract, Hkdf.HASH_LEN]
  rw [Hkdf.hkdf, Hkdf.expand_eq hprk (by decide)]
  simp only [show (64 + Hkdf.HASH_LEN - 1) / Hkdf.HASH_LEN = 2 from rfl]
  rw [show 64 = (Hkdf.blocks (Hkdf.extract (packBytes chainingKey) input) .empty 2).size by
    rw [Hkdf.blocks_size]; rfl, ByteArray.extract_zero_size]
  -- The two blocks of RFC 5869 are the two outputs, with the empty info dropped.
  congr 1

/-- Two errors with one code are of the same kind. -/
theorem NoiseError.code_injective (e₁ e₂ : NoiseError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [NoiseError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Noise
