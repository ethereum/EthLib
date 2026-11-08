module

public import EthLib.Cryptography.Hash.Pbkdf2

/-!
# Proofs: PBKDF2-HMAC-SHA-256

A successful derivation has the requested length and admits only the parameters of RFC 8018 §5.2.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Pbkdf2

/-- Each block appends exactly `hLen` bytes. -/
theorem blocks_size (password salt : ByteArray) (iterations : Nat) (positive : 0 < iterations)
    (count index : Nat) (out : ByteArray) :
    (blocks password salt iterations positive count index out).size =
      out.size + HASH_LEN * count := by
  induction count generalizing index out with
  | zero => simp [blocks]
  | succ count ih =>
    simp only [blocks, ih, ByteArray.size_append]
    simp only [ByteArray.size, Vector.size_toArray, HASH_LEN]
    omega

/-- A successful derivation has exactly the requested number of bytes. -/
theorem pbkdf2_size {password salt key : ByteArray} {iterations length : Nat}
    (h : pbkdf2 password salt iterations length = .ok key) : key.size = length := by
  unfold pbkdf2 at h
  split at h <;> rename_i positive
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · obtain rfl := Except.ok.inj h
          simp only [ByteArray.size_extract, blocks_size, ByteArray.size_empty, HASH_LEN]
          omega
  · contradiction

/-- Zero iterations are rejected for every password, salt and requested length. -/
theorem pbkdf2_zero_iterations (password salt : ByteArray) (length : Nat) :
    pbkdf2 password salt 0 length = .error .zeroIterations := by
  simp [pbkdf2]

/-- A successful derivation uses positive iterations and the RFC's output bounds. -/
theorem pbkdf2_parameters {password salt key : ByteArray} {iterations length : Nat}
    (h : pbkdf2 password salt iterations length = .ok key) :
    0 < iterations ∧ 0 < length ∧ length ≤ MAX_LENGTH := by
  unfold pbkdf2 at h
  split at h <;> rename_i positive
  · split at h <;> rename_i empty
    · contradiction
    · split at h <;> rename_i long
      · contradiction
      · exact ⟨positive, by omega, by omega⟩
  · contradiction

end EthLib.Cryptography.Hash.Pbkdf2
