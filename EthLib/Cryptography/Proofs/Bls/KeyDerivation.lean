module

public import EthLib.Cryptography.Bls.KeyDerivation
public import EthLib.Cryptography.Proofs.Bls.KeyGen
public import EthLib.Cryptography.Proofs.Hash.Hkdf

/-!
# Proofs: ERC-2333 key derivation

The master key is BLS key generation with empty key information.

The Lamport expansion reads 255 HKDF blocks without the checks of HKDF-Expand.

It asks for 255 * 32 bytes, which HKDF accepts and which are 255 whole blocks.

So HKDF gives the same bytes.
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

/-- The Lamport secret key is HKDF of 255 * 32 bytes, cut into 32-byte chunks.

This is ERC-2333 `IKM_to_lamport_SK`, with HKDF-Expand and its checks. -/
theorem ikmToLamportSk_eq_hkdf (ikm salt : ByteArray) :
    (do
      let okm ← Hkdf.hkdf salt ikm ByteArray.empty (LAMPORT_CHUNKS * LAMPORT_CHUNK_SIZE)
      return Vector.ofFn fun (i : Fin 255) =>
        okm.extract (LAMPORT_CHUNK_SIZE * i.val) (LAMPORT_CHUNK_SIZE * (i.val + 1))
      : Except Hkdf.HkdfError (Vector ByteArray 255)) = .ok (ikmToLamportSk ikm salt) := by
  -- The 255 chunks of 32 bytes are exactly 255 whole HKDF blocks.
  rw [show LAMPORT_CHUNKS * LAMPORT_CHUNK_SIZE = Hkdf.HASH_LEN * LAMPORT_CHUNKS from rfl,
    Hkdf.hkdf_hashLen_mul (by decide)]
  unfold ikmToLamportSk
  rw [Hkdf.expandBlocks_empty]
  rfl

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

/-- The Lamport public key is one SHA-256 digest, so it has 32 bytes. -/
@[simp] theorem parentSkToLamportPk_size (parent : SecretKey) (index : UInt32) :
    (parentSkToLamportPk parent index).size = 32 := by
  unfold parentSkToLamportPk
  simp

/-- Child derivation gives a key, or the attempts run out.

Its input keying material is a digest of 32 bytes, so it never rejects a short input. -/
theorem deriveChildSk_eq_ok_or_noKey (parent : SecretKey) (index : UInt32) :
    (∃ sk, deriveChildSk parent index = .ok sk) ∨
      deriveChildSk parent index = .error .keyGenNoKey :=
  keyGen_eq_ok_or_noKey_of_size (by simp) ByteArray.empty

/-- A path of child indices gives a key, or the attempts run out. -/
theorem deriveChildPath_eq_ok_or_noKey (parent : SecretKey) (indices : List UInt32) :
    (∃ sk, deriveChildPath parent indices = .ok sk) ∨
      deriveChildPath parent indices = .error .keyGenNoKey := by
  induction indices generalizing parent with
  | nil => exact Or.inl ⟨parent, rfl⟩
  | cons index rest ih =>
    rw [deriveChildPath]
    rcases deriveChildSk_eq_ok_or_noKey parent index with ⟨child, h⟩ | h
    · rw [h]; exact ih child
    · rw [h]; exact Or.inr rfl

/-- Derivation from a seed fails only on a short seed, or when an attempt runs out.

So a caller of the derivation path can rule out every other error code. -/
theorem derivePath_eq_ikmTooShort_or_ok_or_noKey (seed : ByteArray) (indices : List UInt32) :
    derivePath seed indices = .error (.keyGenIkmTooShort seed.size) ∨
      (∃ sk, derivePath seed indices = .ok sk) ∨
      derivePath seed indices = .error .keyGenNoKey := by
  rw [derivePath]
  rcases keyGen_eq_ikmTooShort_or_ok_or_noKey seed ByteArray.empty with h | ⟨master, h⟩ | h
  · exact Or.inl (by rw [show deriveMasterSk seed = keyGen seed from rfl, h]; rfl)
  · rw [show deriveMasterSk seed = keyGen seed from rfl, h]
    exact Or.inr (deriveChildPath_eq_ok_or_noKey master indices)
  · exact Or.inr (Or.inr (by rw [show deriveMasterSk seed = keyGen seed from rfl, h]; rfl))

end EthLib.Cryptography.Bls.KeyDerivation
