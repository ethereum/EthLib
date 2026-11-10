module

public import EthLib.Execution.Trie.Range
public import EthLib.Execution.Proofs.Trie.Proof

/-!
# Proofs: the range check of a trie

Two errors of the range check with one code come from one constructor.

Every code is at least 201, and differs from every code of a trie or proof error.

So one Python class carries all three.
-/

@[expose] public section

namespace EthLib.Execution.Trie

/-- Two errors with one code come from one constructor. -/
theorem RangeError.code_injective (e₁ e₂ : RangeError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [RangeError.code] at h; exact absurd h (by decide))

/-- Every code of the range check is at least 201. -/
theorem RangeError.le_code (e : RangeError) : 201 ≤ e.code.toNat := by
  cases e <;> simp only [RangeError.code] <;> decide

/-- A range error never has the code of a trie error, so one Python class carries both. -/
theorem RangeError.code_ne_trie (e : RangeError) (r : TrieError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [RangeError.code, TrieError.code] <;> decide

/-- A range error never has the code of a proof error, so one Python class carries both. -/
theorem RangeError.code_ne_proof (e : RangeError) (r : ProofError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [RangeError.code, ProofError.code] <;> decide

end EthLib.Execution.Trie
