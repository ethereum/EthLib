module

public import EthLib.Cryptography.Hash.Scrypt
public import EthLib.Cryptography.Proofs.Hash.Pbkdf2

/-!
# Proofs: scrypt

The scrypt steps preserve their block sizes, and derivation returns the requested key length.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Scrypt

/-- A successful Salsa20/8 call returns one 64-byte block. -/
theorem salsa208_size {input output : ByteArray} (h : salsa208 input = .ok output) :
    output.size = 64 := by
  unfold salsa208 at h
  split at h
  · obtain rfl := Except.ok.inj h
    exact State.bytes_size _
  · contradiction

/-- A successful BlockMix call returns `128 * r` bytes. -/
theorem blockMix_size {input output : ByteArray} {r : Nat}
    (h : blockMix input r = .ok output) : output.size = 128 * r := by
  unfold blockMix at h
  split at h
  · split at h
    · obtain rfl := Except.ok.inj h
      exact (blockMixCore _ _ _).property
    · contradiction
  · contradiction

/-- A successful ROMix call returns `128 * r` bytes. -/
theorem romix_size {input output : ByteArray} {n r : Nat}
    (h : romix input n r = .ok output) : output.size = 128 * r := by
  unfold romix at h
  split at h
  · split at h
    · split at h
      · obtain rfl := Except.ok.inj h
        exact (romixCore _ _ _ _ _).property
      · contradiction
    · contradiction
  · contradiction

/-- A successful scrypt call returns the requested number of bytes. -/
theorem scrypt_size {password salt key : ByteArray} {n r p length : Nat}
    (h : scrypt password salt n r p length = .ok key) : key.size = length := by
  unfold scrypt at h
  simp only [bind, Except.bind, MonadExcept.throw, Except.mapError] at h
  repeat first | contradiction | split at h
  obtain rfl := Except.ok.inj h
  exact Pbkdf2.pbkdf2_size (by assumption)

end EthLib.Cryptography.Hash.Scrypt
