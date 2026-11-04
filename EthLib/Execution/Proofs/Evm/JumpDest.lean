module

public import EthLib.Execution.Evm.JumpDest

/-!
# Proofs: `Evm.JumpDest`

A position is a valid jump destination exactly when a JUMPDEST opcode starts there.

So each valid destination holds the byte `0x5b`.

No position between an opcode and the next one is valid, so the data of a PUSH holds none.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- The next opcode starts after the current one. -/
theorem lt_nextOpcode (code : ByteArray) (pc : Nat) : pc < nextOpcode code pc := by
  unfold nextOpcode
  split <;> omega

/-- The scan from `pc` lists positions from `pc` on, and within the code. -/
theorem le_of_mem_opcodePositionsFrom {code : ByteArray} {fuel pc x : Nat}
    (h : x ∈ opcodePositionsFrom code fuel pc) : pc ≤ x ∧ x < code.size := by
  induction fuel generalizing pc with
  | zero => simp [opcodePositionsFrom] at h
  | succ fuel ih =>
    unfold opcodePositionsFrom at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := ih h
        have := lt_nextOpcode code pc
        omega
    · simp at h

/-- No position between an opcode and the next one starts an opcode. -/
theorem not_mem_of_lt_nextOpcode {code : ByteArray} {fuel pc p q : Nat}
    (hp : p ∈ opcodePositionsFrom code fuel pc) (lo : p < q) (hi : q < nextOpcode code p) :
    q ∉ opcodePositionsFrom code fuel pc := by
  induction fuel generalizing pc with
  | zero => simp [opcodePositionsFrom] at hp
  | succ fuel ih =>
    unfold opcodePositionsFrom at hp ⊢
    split at hp
    · rename_i hpc
      simp only [hpc, ite_true, List.mem_cons, not_or]
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨by omega, fun hq => ?_⟩
        -- Every later position is at or after the next opcode.
        have := (le_of_mem_opcodePositionsFrom hq).1
        omega
      · have := (le_of_mem_opcodePositionsFrom hp).1
        have := lt_nextOpcode code pc
        exact ⟨by omega, ih hp⟩
    · simp at hp

/-- Marking the JUMPDEST bytes of a list of positions sets exactly those flags. -/
theorem getD_foldl_mark {code : ByteArray} (positions : List Nat) (flags : Array Bool)
    (hsize : flags.size = code.size) (hlt : ∀ x ∈ positions, x < code.size) (i : Nat) :
    (positions.foldl
        (fun flags pc => if byteAt code pc = JUMPDEST then flags.set! pc true else flags)
        flags).getD i false = true ↔
      flags.getD i false = true ∨ (i ∈ positions ∧ byteAt code i = JUMPDEST) := by
  induction positions generalizing flags with
  | nil => simp
  | cons pc rest ih =>
    simp only [List.foldl_cons]
    have hpc := hlt pc List.mem_cons_self
    have hrest : ∀ x ∈ rest, x < code.size := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    split
    · rename_i hj
      rw [ih _ (by simp [hsize]) hrest]
      by_cases hi : i = pc
      · subst hi
        simp [Array.getD_eq_getD_getElem?, hj, hsize, hpc]
      · simp [Array.getD_eq_getD_getElem?, Ne.symm hi, hi]
    · rename_i hj
      rw [ih _ hsize hrest]
      by_cases hi : i = pc
      · subst hi
        simp [hj]
      · simp [hi]

/-- A position is a valid destination exactly when an opcode starts there with the byte JUMPDEST. -/
theorem isValidJumpDest_iff {code : ByteArray} {i : Nat} :
    isValidJumpDest (validJumpDestinations code) i = true ↔
      i ∈ opcodePositions code ∧ byteAt code i = JUMPDEST := by
  unfold isValidJumpDest validJumpDestinations
  rw [getD_foldl_mark (opcodePositions code) _ (by simp)
    fun x hx => (le_of_mem_opcodePositionsFrom hx).2]
  -- No flag is set before the scan.
  have unset : (Array.replicate code.size false).getD i false = false := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  simp [unset]

/-- Each valid jump destination holds the byte `0x5b`. -/
theorem byteAt_of_isValidJumpDest {code : ByteArray} {i : Nat}
    (h : isValidJumpDest (validJumpDestinations code) i = true) : byteAt code i = 0x5b :=
  (isValidJumpDest_iff.mp h).2

/-- No position in the data of a PUSH, or between two opcodes, is a valid jump destination. -/
theorem not_isValidJumpDest_of_lt_nextOpcode {code : ByteArray} {p q : Nat}
    (hp : p ∈ opcodePositions code) (lo : p < q) (hi : q < nextOpcode code p) :
    isValidJumpDest (validJumpDestinations code) q = false := by
  have := not_mem_of_lt_nextOpcode hp lo hi
  cases h : isValidJumpDest (validJumpDestinations code) q
  · rfl
  · exact absurd (isValidJumpDest_iff.mp h).1 this

end EthLib.Execution.Evm
