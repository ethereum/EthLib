module

public import EthLib.Execution.Evm.Machine.JumpDest
public import EthLib.Execution.Proofs.Evm.Op

/-!
# Proofs: `Evm.Machine.JumpDest`

A position is a valid jump destination exactly when a JUMPDEST opcode starts there.

So each valid destination holds the byte `0x5b`.

No position between an opcode and the next one is valid, so the data of a PUSH holds none.

A relation states the opcode boundaries by the step rule alone, and the scan lists exactly them.

So a position is a valid jump destination exactly when it is a boundary that holds JUMPDEST.

The step past a PUSH1 to PUSH32 skips its data, by the byte alone.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (byteAt)

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
    next hpc =>
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
    next hj =>
      rw [ih _ (by simp [hsize]) hrest]
      by_cases hi : i = pc
      · subst hi
        simp [Array.getD_eq_getD_getElem?, hj, hsize, hpc]
      · simp [Array.getD_eq_getD_getElem?, Ne.symm hi, hi]
    next hj =>
      rw [ih _ hsize hrest]
      by_cases hi : i = pc
      · subst hi
        simp [hj]
      · simp [hi]

/-- The scan that marks the flags visits the listed opcode positions, in order. -/
theorem markJumpDestsFrom_eq_foldl (code : ByteArray) (fuel pc : Nat) (flags : Array Bool) :
    markJumpDestsFrom code fuel pc flags =
      (opcodePositionsFrom code fuel pc).foldl
        (fun flags pc => if byteAt code pc = JUMPDEST then flags.set! pc true else flags)
        flags := by
  induction fuel generalizing pc flags with
  | zero => simp [markJumpDestsFrom, opcodePositionsFrom]
  | succ fuel ih =>
    unfold markJumpDestsFrom opcodePositionsFrom
    split
    · rw [ih]
      rfl
    · rfl

/-- The valid jump destinations mark each listed opcode position that holds JUMPDEST. -/
theorem validJumpDestinations_eq_foldl (code : ByteArray) :
    validJumpDestinations code =
      (opcodePositions code).foldl
        (fun flags pc => if byteAt code pc = JUMPDEST then flags.set! pc true else flags)
        (Array.replicate code.size false) :=
  markJumpDestsFrom_eq_foldl code code.size 0 _

/-- A position is a valid destination exactly when an opcode starts there with the byte JUMPDEST. -/
theorem isValidJumpDest_iff {code : ByteArray} {i : Nat} :
    isValidJumpDest (validJumpDestinations code) i = true ↔
      i ∈ opcodePositions code ∧ byteAt code i = JUMPDEST := by
  rw [validJumpDestinations_eq_foldl]
  unfold isValidJumpDest
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

/-! ## Boundaries by the step rule -/

/-- The opcode boundaries of the code from `start`, by the step rule alone.

The start is a boundary, and so is each position that the next opcode reaches in the code. -/
inductive BoundaryFrom (code : ByteArray) : Nat → Nat → Prop
  | here {start : Nat} : start < code.size → BoundaryFrom code start start
  | step {start pc : Nat} : start < code.size → BoundaryFrom code (nextOpcode code start) pc →
      BoundaryFrom code start pc

/-- A boundary lies in the code, at or after the start. -/
theorem BoundaryFrom.bounds {code : ByteArray} {start pc : Nat} (h : BoundaryFrom code start pc) :
    start ≤ pc ∧ pc < code.size := by
  induction h with
  | here h => exact ⟨Nat.le_refl _, h⟩
  | @step start pc _ _ ih =>
    have := lt_nextOpcode code start
    exact ⟨by omega, ih.2⟩

/-- Each position that the scan lists is a boundary. -/
theorem boundaryFrom_of_mem_opcodePositionsFrom {code : ByteArray} {fuel start pc : Nat}
    (h : pc ∈ opcodePositionsFrom code fuel start) : BoundaryFrom code start pc := by
  induction fuel generalizing start with
  | zero => simp [opcodePositionsFrom] at h
  | succ fuel ih =>
    unfold opcodePositionsFrom at h
    split at h
    next hs =>
      rcases List.mem_cons.mp h with rfl | h
      · exact .here hs
      · exact .step hs (ih h)
    · simp at h

/-- The scan lists each boundary that lies fewer than `fuel` bytes past the start. -/
theorem mem_opcodePositionsFrom_of_boundaryFrom {code : ByteArray} {start pc : Nat}
    (h : BoundaryFrom code start pc) {fuel : Nat} (hfuel : pc - start < fuel) :
    pc ∈ opcodePositionsFrom code fuel start := by
  induction h generalizing fuel with
  | here hs =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [opcodePositionsFrom, hs]
  | @step start pc hs rest ih =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlt := lt_nextOpcode code start
    have hb := rest.bounds
    unfold opcodePositionsFrom
    simp only [hs, ↓reduceIte]
    exact List.mem_cons_of_mem _ (ih (by omega))

/-- The scan of the code lists exactly the boundaries from position 0. -/
theorem mem_opcodePositions_iff {code : ByteArray} {pc : Nat} :
    pc ∈ opcodePositions code ↔ BoundaryFrom code 0 pc := by
  constructor
  · exact boundaryFrom_of_mem_opcodePositionsFrom
  · intro h
    exact mem_opcodePositionsFrom_of_boundaryFrom h (by have := h.bounds; omega)

/-- A position is a valid jump destination exactly when it is a boundary that holds JUMPDEST.

The boundaries start at position 0. -/
theorem isValidJumpDest_iff_boundaryFrom {code : ByteArray} {i : Nat} :
    isValidJumpDest (validJumpDestinations code) i = true ↔
      BoundaryFrom code 0 i ∧ byteAt code i = JUMPDEST := by
  rw [isValidJumpDest_iff, mem_opcodePositions_iff]

/-- The next opcode follows the byte at `pc`, and the data of a PUSH1 to PUSH32.

The bytes `0x60` to `0x7f` are PUSH1 to PUSH32, with 1 to 32 bytes of data.

So the rule needs no decoder. -/
theorem nextOpcode_eq (code : ByteArray) (pc : Nat) :
    nextOpcode code pc =
      pc + 1 + if 0x60 ≤ (byteAt code pc).toNat ∧ (byteAt code pc).toNat ≤ 0x7f then
        (byteAt code pc).toNat - 0x5f else 0 := by
  unfold nextOpcode
  generalize byteAt code pc = b
  split
  next n hd =>
    -- A PUSH decodes only from its own byte.
    have := congrArg UInt8.toNat (Op.toByte_of_decode hd)
    simp only [Op.toByte, Nat.toUInt8, UInt8.ofNat_add, UInt8.reduceOfNat, UInt8.toNat_add,
      UInt8.reduceToNat, UInt8.toNat_ofNat', Nat.reducePow, Nat.add_mod_mod] at this
    have := n.isLt
    split <;> omega
  next hnp =>
    -- A byte of PUSH1 to PUSH32 decodes to a PUSH.
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨h1, h2⟩ =>
      hnp ⟨b.toNat - 0x5f, by omega⟩ (by simp [Op.decode, show 0x5f ≤ b.toNat by omega, h2]))]

end EthLib.Execution.Evm
