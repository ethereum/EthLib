module

public import EthLib.Cryptography.Hash.Pbkdf2

/-!
# Proofs: PBKDF2-HMAC-SHA-256

The derivation succeeds exactly for the parameters of RFC 8018 §5.2 and inputs that SHA-256 admits.

A successful derivation has exactly the requested length.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Pbkdf2

/-- Each block appends exactly `hLen` bytes. -/
theorem blocks_size (password salt : ByteArray) (iterations count index : Nat) (out : ByteArray) :
    (blocks password salt iterations count index out).size = out.size + HASH_LEN * count := by
  induction count generalizing index out with
  | zero => simp [blocks]
  | succ count ih =>
    simp only [blocks, ih, ByteArray.size_append]
    simp only [ByteArray.size, Vector.size_toArray, HASH_LEN]
    omega

/--
The derivation succeeds exactly when its parameters and the inputs of HMAC are within bounds.

RFC 8018 §5.2 bounds the parameters, and SHA-256 bounds the inputs.

The key is then the first `dkLen` bytes of the blocks.
-/
theorem pbkdf2_eq_ok_iff {password salt key : ByteArray} {iterations length : Nat} :
    pbkdf2 password salt iterations length = .ok key ↔
      (0 < iterations ∧ 0 < length ∧ length ≤ MAX_LENGTH ∧ password.size < 2 ^ 61 ∧
        64 + salt.size + 4 < 2 ^ 61) ∧
      key = (blocks password salt iterations ((length + HASH_LEN - 1) / HASH_LEN) 1
        ByteArray.empty).extract 0 length := by
  unfold pbkdf2
  by_cases zero : iterations = 0
  · simp [zero]
  by_cases empty : length = 0
  · simp [zero, empty]
  by_cases long : MAX_LENGTH < length
  · simp only [zero, empty, long, ite_true, ite_false, reduceCtorEq, false_iff]
    omega
  by_cases input : 2 ^ 61 ≤ password.size ∨ 2 ^ 61 ≤ 64 + salt.size + 4
  · simp only [zero, empty, long, input, ite_true, ite_false, reduceCtorEq, false_iff]
    omega
  simp only [zero, empty, long, input, ite_false, Except.ok.injEq]
  constructor
  · rintro rfl
    exact ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, rfl⟩
  · rintro ⟨-, rfl⟩
    rfl

/-- The derivation succeeds exactly when the parameters and the input sizes are within bounds. -/
theorem pbkdf2_ok_iff {password salt : ByteArray} {iterations length : Nat} :
    (∃ key, pbkdf2 password salt iterations length = .ok key) ↔
      0 < iterations ∧ 0 < length ∧ length ≤ MAX_LENGTH ∧ password.size < 2 ^ 61 ∧
        64 + salt.size + 4 < 2 ^ 61 := by
  simp only [pbkdf2_eq_ok_iff, exists_and_left, exists_eq, and_true]

/-- A successful derivation has exactly the requested number of bytes. -/
theorem pbkdf2_size {password salt key : ByteArray} {iterations length : Nat}
    (h : pbkdf2 password salt iterations length = .ok key) : key.size = length := by
  obtain ⟨-, rfl⟩ := pbkdf2_eq_ok_iff.mp h
  simp only [ByteArray.size_extract, blocks_size, ByteArray.size_empty, HASH_LEN]
  omega

/-- Zero iterations are rejected for every password, salt and requested length. -/
theorem pbkdf2_zero_iterations (password salt : ByteArray) (length : Nat) :
    pbkdf2 password salt 0 length = .error .zeroIterations := by
  simp [pbkdf2]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem Pbkdf2Error.code_injective (e₁ e₂ : Pbkdf2Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Pbkdf2Error.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Hash.Pbkdf2
