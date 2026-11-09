module

public import EthLib.Cryptography.Bls.KeyDerivation
public import EthLib.Cryptography.Proofs.Bls.KeyGen

/-!
# Proofs: ERC-2333 key derivation

The master key is the existing BLS key generation with empty key information.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyDerivation

open EthLib.Cryptography.Bls.Signatures

/-- Master derivation reuses BLS key generation, ERC-2333, `hkdf_mod_r()` rationale. -/
theorem derive_master_sk_eq_key_gen (seed : ByteArray) :
    deriveMasterSk seed = keyGen seed := rfl

/-- Every successful BLS key generation is the ERC-2333 master key of the same seed. -/
theorem derive_master_sk_eq_ok_of_key_gen {seed : ByteArray} {key : SecretKey}
    (h : keyGen seed = .ok key) : deriveMasterSk seed = .ok key := h

/-- Master derivation rejects a seed shorter than 32 bytes. -/
theorem derive_master_sk_seed_too_short {seed : ByteArray} (h : seed.size < 32) :
    deriveMasterSk seed = .error (.keyGenIkmTooShort seed.size) :=
  keyGen_ikmTooShort h _

/-- A path with no indices leaves the parent unchanged. -/
theorem derive_child_path_nil (parent : SecretKey) : deriveChildPath parent [] = .ok parent :=
  rfl

/-- A master-only path returns the master key. -/
theorem derive_path_nil (seed : ByteArray) : derivePath seed [] = deriveMasterSk seed := by
  simp only [derivePath]
  cases deriveMasterSk seed <;> rfl

end EthLib.Cryptography.Bls.KeyDerivation
