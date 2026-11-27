module

public import EthLib.Execution.Proofs.Evm.Logic.MeterReach
public import EthLib.Execution.Proofs.Evm.Logic.Cost

/-!
# Proofs: costs under the state gas meter

A cost over checked code under one counter bounds the gas that the state gas meter spends.

It bounds the execution gas and the reservoir together, along a run that sends no message.

Source: the reservoir of [EIP-8037][eip8037].

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

variable {fork : EthLib.Base.Fork}

/-- A cost over checked code holds under the state gas meter, on the execution gas and reservoir.

The frames of the postcondition stop with no error, or with a revert. -/
theorem Costs.covered {P Q : Evm fork Nat → Prop} {cost : Nat} (h : Costs (Step fork) P Q cost)
    -- Each frame of the precondition has checked code, its flags, an opcode position and no error.
    (ready : ∀ low, P low → SupportedCode low.code = true ∧
      low.validJumpDestinations = validJumpDestinations low.code ∧
      (low.code.size ≤ low.pc ∨ low.pc ∈ opcodePositions low.code) ∧ low.error = none)
    (ends : ∀ low, Q low → low.running = false ∧ Carried low.error)
    {high : Evm fork StateGasMeter} (covered : Covered P high) :
    ∃ after, Reaches (Step fork) high after ∧ Covered Q after ∧
      high.gas.gasLeft + high.gas.reservoir ≤ after.gas.gasLeft + after.gas.reservoir + cost := by
  obtain ⟨low, hp, ⟨meter, below, rfl⟩, fits⟩ := covered
  obtain ⟨supported, flags, boundary, start⟩ := ready low hp
  obtain ⟨after, reached, hq, paid⟩ := h low hp
  obtain ⟨stopped, carried⟩ := ends after hq
  obtain ⟨high', covers, highReached, ledger⟩ := reached.meterCovers supported flags boundary
    (fun _ => start) carried ⟨fits, .inl ⟨meter, below, rfl⟩⟩
  -- The ledger starts with the excess of the execution gas and the reservoir over the counter.
  have kept := ledger (meter.gasLeft + meter.reservoir - low.gas) (by
    simp only [Ledger, gas_withStateGas]
    omega)
  obtain ⟨m, hm, rfl⟩ := covers.followsMeter_of_stopped stopped
  refine ⟨_, highReached, ⟨after, hq, ⟨m, hm, rfl⟩, covers.1⟩, ?_⟩
  simp only [Ledger, gas_withStateGas] at kept ⊢
  omega

end EthLib.Execution.Evm.Logic
