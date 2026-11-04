module

public import EthLib.Serialization.Ssz.Codec.Error

/-!
# Proofs: the codes of SSZ refusals

Each constructor has its own code.

So the code of a refusal names the constructor it came from.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The code of a refusal is one more than the position of its constructor. -/
theorem Err.code_eq_ctorIdx (e : Err) : e.code = UInt32.ofNat (e.ctorIdx + 1) := by
  cases e <;> rfl

/-- Two refusals with one code come from one constructor. -/
theorem Err.code_injective (e₁ e₂ : Err) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Every position is small, so adding one and reading it as a 32-bit integer never wraps.
  have small (e : Err) : e.ctorIdx < 75 := by cases e <;> simp [Err.ctorIdx]
  have h₁ := small e₁
  have h₂ := small e₂
  rw [Err.code_eq_ctorIdx, Err.code_eq_ctorIdx] at h
  have := congrArg UInt32.toNat h
  simp only [UInt32.toNat_ofNat'] at this
  omega

end EthLib.Serialization.Ssz
