module

public import EthLib.Cryptography.Bls.KeyDerivation
public import EthLib.Cryptography.Proofs.Bls.KeyGen
public import EthLib.Cryptography.Proofs.Hash.Hkdf

/-!
# Proofs: ERC-2333 key derivation

The master key is the existing BLS key generation with empty key information.

The Lamport expansion asks HKDF for exactly 255 × 32 bytes, its largest output, so it never fails.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyDerivation

open EthLib.Cryptography.Bls.Signatures
open EthLib.Cryptography.Hash

/-- BLS error codes lie below 101, the first code of a path error. -/
theorem _root_.EthLib.Cryptography.Bls.BlsError.code_lt (e : BlsError) : e.code < 101 := by
  cases e <;> simp [BlsError.code]

/-- Master derivation reuses BLS key generation, ERC-2333, `hkdf_mod_r()` rationale. -/
theorem deriveMasterSk_eq_keyGen (seed : ByteArray) :
    deriveMasterSk seed = keyGen seed := rfl

/-- Master derivation rejects a seed shorter than 32 bytes. -/
theorem deriveMasterSk_ikmTooShort {seed : ByteArray} (h : seed.size < 32) :
    deriveMasterSk seed = .error (.keyGenIkmTooShort seed.size) :=
  keyGen_ikmTooShort h _

/-- The Lamport expansion is exactly HKDF's maximum output length, so it cannot fail. -/
theorem expand_eq_ok_lamport (ikm salt : ByteArray) :
    Hkdf.expand (Hkdf.extract salt ikm) ByteArray.empty
      (LAMPORT_CHUNKS * LAMPORT_CHUNK_SIZE) =
      .ok (Hkdf.expandBlocks (Hkdf.extract salt ikm) ByteArray.empty ByteArray.empty
        1 LAMPORT_CHUNKS) := by
  simp only [Hkdf.expand, Hkdf.extract, Hmac.hmac_size, Hkdf.HASH_LEN,
    LAMPORT_CHUNKS, LAMPORT_CHUNK_SIZE]
  simp only [show ¬ 32 < 32 by decide, show ¬ 255 * 32 < 255 * 32 by decide, ite_false]
  have hsize := Hkdf.expandBlocks_size (Hmac.hmac salt ikm)
    ByteArray.empty ByteArray.empty 1 255
  change (Except.ok ((Hkdf.expandBlocks (Hmac.hmac salt ikm) ByteArray.empty ByteArray.empty
    1 255).extract 0 (Hkdf.HASH_LEN * 255)) : Except Hkdf.HkdfError ByteArray) = _
  rw [← hsize, ByteArray.extract_zero_size]

/-- Child derivation never fails in HKDF, as key generation never does. -/
theorem deriveChildSk_ne_hkdf (parent : SecretKey) (index : UInt32) :
    deriveChildSk parent index ≠ .error .keyGenHkdf :=
  keyGen_ne_hkdf (parentSkToLamportPk parent index) ByteArray.empty

/-- A path with no indices leaves the parent unchanged. -/
theorem deriveChildPath_nil (parent : SecretKey) : deriveChildPath parent [] = .ok parent :=
  rfl

/-- A master-only path returns the master key. -/
theorem derivePath_nil (seed : ByteArray) : derivePath seed [] = deriveMasterSk seed := by
  simp only [derivePath]
  cases deriveMasterSk seed <;> rfl

end EthLib.Cryptography.Bls.KeyDerivation
