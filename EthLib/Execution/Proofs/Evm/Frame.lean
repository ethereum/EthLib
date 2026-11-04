module

public import EthLib.Execution.Evm.Frame

/-!
# Proofs: `Evm.Frame`

With one counter of gas, a charge succeeds exactly when the frame has the gas.

It then takes the charge from the gas left, and changes nothing else.
-/

@[expose] public section

namespace EthLib.Execution.Evm

variable {fork : EthLib.Base.Fork}

/-- With one counter of gas, a charge fails exactly when it is above the gas left. -/
theorem chargeGas_eq_error_iff {evm : Evm fork Nat} {amount : Nat} {e : EvmError} :
    chargeGas evm amount = .error e ↔ evm.gas < amount ∧ e = .outOfGas := by
  simp only [chargeGas, GasMeter.charge]
  split
  · simp_all [bind, Except.bind, eq_comm]
  · simp only [bind, Except.bind, pure, Except.pure, reduceCtorEq, false_iff, not_and]
    intro
    omega

/-- With one counter of gas, a charge within the gas left takes it from the gas left. -/
theorem chargeGas_eq_ok_iff {evm after : Evm fork Nat} {amount : Nat} :
    chargeGas evm amount = .ok after ↔
      amount ≤ evm.gas ∧ after = { evm with gas := evm.gas - amount } := by
  simp only [chargeGas, GasMeter.charge]
  split
  · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
    intro
    omega
  · simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro rfl
      exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

end EthLib.Execution.Evm
