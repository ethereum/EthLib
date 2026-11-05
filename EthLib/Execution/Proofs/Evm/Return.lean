module

public import EthLib.Execution.Evm.Return
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Return`

RETURN and REVERT pay the growth of memory, then stop with the memory range as their output.

REVERT succeeds as a step, with the revert error in the frame, so it keeps the gas it has left.

Neither changes the message, the state or the substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)

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

end EthLib.Execution.Evm
