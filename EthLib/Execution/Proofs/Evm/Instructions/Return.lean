module

public import EthLib.Execution.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.Return`

RETURN and REVERT pay the growth of memory, then stop with the memory range as their output.

REVERT succeeds as a step, with the revert error in the frame, so it keeps the gas it has left.

Neither changes the message, the state or the substate.

Their output has the size of the range.

It holds the bytes of memory in the range, and reads as zero past its end.

Both keep the size of memory a multiple of 32.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 byteAt byteAt_of_size_le)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- RETURN pays the growth of memory, then stops with the bytes of memory as output. -/
theorem returnStep_cons {evm : Evm fork Meter} {start size : U256} {rest : List U256}
    (h : evm.stack.val = start :: size :: rest) :
    returnStep evm =
      (GasMeter.charge evm.gas (extendMemory evm.memory.size [(start, size)]).cost).map
        fun gas =>
          let memory :=
            memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy
          { evm with
            stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩
            gas
            memory
            output := memoryReadBytes memory start.toNat size.toNat
            running := false } := by
  have hstack : evm.stack = ⟨start :: size :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  simp only [returnStep, haltWithOutput, popWord, chargeGasAndMemory, chargeGas, hstack,
    Stack.pop, Nat.zero_add]
  rcases hc : GasMeter.charge evm.gas _ with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map]

/-- REVERT is RETURN with the revert error in the frame. -/
theorem revertStep_eq (evm : Evm fork Meter) :
    revertStep evm = (returnStep evm).map fun evm => { evm with error := some .revert } := by
  simp only [revertStep, returnStep]
  rcases haltWithOutput evm with _ | _ <;> rfl

/-- RETURN keeps the message, the state and the substate. -/
theorem returnStep_sameContext {evm after : Evm fork Meter} (h : returnStep evm = .ok after) :
    SameContext evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have := ((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (chargeGasAndMemory_sameContext h3)
  exact ⟨this.message, this.state, this.substate⟩

/-- REVERT keeps the message, the state and the substate. -/
theorem revertStep_sameContext {evm after : Evm fork Meter} (h : revertStep evm = .ok after) :
    SameContext evm after := by
  obtain ⟨e, he, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have := returnStep_sameContext he
  exact ⟨this.message, this.state, this.substate⟩

/-- RETURN and REVERT output as many bytes as their size.

Memory must start at a size that is a multiple of 32. -/
theorem size_output_haltWithOutput {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0)
    (h : haltWithOutput evm = .ok after) : after.output.size = size.toNat := by
  unfold haltWithOutput at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, s1, m1, -⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, -, m2, -⟩ := popWord_of_stack s1 h2
  by_cases hz : size = 0
  · subst hz
    simp [memoryReadBytes]
  · have hmod2 : e2.memory.size % 32 = 0 := by rw [m2, m1]; exact hmod
    have fit := le_size_chargeGasAndMemory hmod2 h3 (start, size) (by simp) hz
    simp only at fit
    exact size_memoryReadBytes fit

/-- RETURN and REVERT output the bytes of memory from their start, with zero past the size.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_output_haltWithOutput {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0)
    (h : haltWithOutput evm = .ok after) (i : Nat) :
    byteAt after.output i = if i < size.toNat then byteAt evm.memory (start.toNat + i) else 0 := by
  unfold haltWithOutput at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, s1, m1, -⟩ := popWord_of_stack hstack h1
  obtain ⟨rfl, -, m2, -⟩ := popWord_of_stack s1 h2
  by_cases hz : size = 0
  · subst hz
    simp only [memoryReadBytes]
    exact byteAt_of_size_le (by simp)
  · have hmod2 : e2.memory.size % 32 = 0 := by rw [m2, m1]; exact hmod
    have fit := le_size_chargeGasAndMemory hmod2 h3 (start, size) (by simp) hz
    simp only at fit
    rw [byteAt_memoryReadBytes fit]
    split
    · rw [byteAt_chargeGasAndMemory h3, m2, m1]
    · rfl

/-- RETURN outputs as many bytes as its size.

Memory must start at a size that is a multiple of 32. -/
theorem size_output_returnStep {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0)
    (h : returnStep evm = .ok after) : after.output.size = size.toNat :=
  size_output_haltWithOutput hstack hmod h

/-- RETURN outputs the bytes of memory from its start, with zero past the size.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_output_returnStep {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0)
    (h : returnStep evm = .ok after) (i : Nat) :
    byteAt after.output i = if i < size.toNat then byteAt evm.memory (start.toNat + i) else 0 :=
  byteAt_output_haltWithOutput hstack hmod h i

/-- REVERT outputs as many bytes as its size.

Memory must start at a size that is a multiple of 32. -/
theorem size_output_revertStep {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0)
    (h : revertStep evm = .ok after) : after.output.size = size.toNat := by
  unfold revertStep at h
  obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact size_output_haltWithOutput (after := mid) hstack hmod hmid

/-- REVERT outputs the bytes of memory from its start, with zero past the size.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_output_revertStep {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0)
    (h : revertStep evm = .ok after) (i : Nat) :
    byteAt after.output i = if i < size.toNat then byteAt evm.memory (start.toNat + i) else 0 := by
  unfold revertStep at h
  obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact byteAt_output_haltWithOutput (after := mid) hstack hmod hmid i

/-- A halt with output keeps the size of memory a multiple of 32. -/
theorem size_haltWithOutput_mod {evm after : Evm fork Meter} (hmod : evm.memory.size % 32 = 0)
    (h : haltWithOutput evm = .ok after) : after.memory.size % 32 = 0 := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (size_chargeGasAndMemory_mod
    (by rw [(popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod) h3 :
    e3.memory.size % 32 = 0)

/-- RETURN and REVERT keep the size of memory a multiple of 32. -/
theorem size_returnOpStep_mod {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : step evm = .ok after) :
    after.memory.size % 32 = 0 := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  · subst hstep
    exact size_haltWithOutput_mod hmod h
  · split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (size_haltWithOutput_mod hmod h1 : e.memory.size % 32 = 0)
    · cases hstep

end EthLib.Execution.Evm
