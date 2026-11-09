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

/-- The expansion of the input to a Lamport secret key never fails. -/
theorem ikmToLamportSk_ne_error (ikm salt : ByteArray) (e : BlsError) :
    ikmToLamportSk ikm salt ≠ .error e := by
  have hok : ∀ e', Hkdf.hkdf salt ikm ByteArray.empty (LAMPORT_CHUNKS * LAMPORT_CHUNK_SIZE) ≠
      .error e' := fun e' h => by
    have := (Hkdf.hkdf_eq_error_iff.mp h).2
    simp [LAMPORT_CHUNKS, LAMPORT_CHUNK_SIZE, Hkdf.HASH_LEN] at this
  unfold ikmToLamportSk
  unfold Hkdf.hkdf at hok
  cases h : Hkdf.expand (Hkdf.extract salt ikm) ByteArray.empty
      (LAMPORT_CHUNKS * LAMPORT_CHUNK_SIZE) with
  | error e' => exact absurd h (hok e')
  | ok bytes => intro h; cases h

/-- The compressed Lamport public key never fails. -/
theorem parentSkToLamportPk_ne_error (parent : SecretKey) (index : UInt32) (e : BlsError) :
    parentSkToLamportPk parent index ≠ .error e := by
  unfold parentSkToLamportPk
  cases h₁ : ikmToLamportSk (Fr.toBytesBE parent.val) (Base.natToBytes4 index.toNat) with
  | error e' => exact absurd h₁ (ikmToLamportSk_ne_error _ _ e')
  | ok first =>
    cases h₂ : ikmToLamportSk ⟨(Fr.toBytesBE parent.val).data.map (~~~ ·)⟩
        (Base.natToBytes4 index.toNat) with
    | error e' => exact absurd h₂ (ikmToLamportSk_ne_error _ _ e')
    | ok second => simp [h₁, h₂, bind, Except.bind, pure, Except.pure]

/-- Child derivation never fails in HKDF, as key generation never does. -/
theorem deriveChildSk_ne_hkdf (parent : SecretKey) (index : UInt32) :
    deriveChildSk parent index ≠ .error .keyGenHkdf := by
  unfold deriveChildSk
  cases h : parentSkToLamportPk parent index with
  | error e => exact absurd h (parentSkToLamportPk_ne_error _ _ e)
  | ok compressed => simpa [bind, Except.bind] using keyGen_ne_hkdf compressed ByteArray.empty

/-- A path with no indices leaves the parent unchanged. -/
theorem deriveChildPath_nil (parent : SecretKey) : deriveChildPath parent [] = .ok parent :=
  rfl

/-- A master-only path returns the master key. -/
theorem derivePath_nil (seed : ByteArray) : derivePath seed [] = deriveMasterSk seed := by
  simp only [derivePath]
  cases deriveMasterSk seed <;> rfl

end EthLib.Cryptography.Bls.KeyDerivation
