module

public import EthLib.Execution.Evm.ControlFlow
public import EthLib.Execution.Proofs.Evm.JumpDest

/-!
# Proofs: `Evm.ControlFlow`

JUMP that pays fails exactly when its destination is not a valid jump destination.

Otherwise it moves the program counter to the destination.

JUMPI with a zero condition goes to the next opcode, whatever the destination.

JUMPI with another condition fails exactly as JUMP does.

When the frame holds the flags of its code, the valid destinations are the JUMPDEST opcodes.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256)
open GasCosts

variable {Meter : Type} [GasMeter Meter]

/-- JUMP that pays fails exactly when its destination is not valid. -/
theorem jumpStep_eq_error_iff {evm : Evm Meter} {destination : U256} {rest : List U256}
    {gas : Meter} (h : evm.stack.val = destination :: rest)
    (paid : GasMeter.charge evm.gas OPCODE_JUMP = .ok gas) :
    jumpStep evm = .error .invalidJumpDest ↔
      isValidJumpDest evm.validJumpDestinations destination.toNat = false := by
  have hstack : evm.stack = ⟨destination :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  simp only [jumpStep, popWord, chargeGas, hstack, Stack.pop]
  cases hv : isValidJumpDest evm.validJumpDestinations destination.toNat <;>
    simp [paid, hv, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- JUMP that pays, to a valid destination, moves the program counter there. -/
theorem jumpStep_of_isValidJumpDest {evm : Evm Meter} {destination : U256} {rest : List U256}
    {gas : Meter} (h : evm.stack.val = destination :: rest)
    (paid : GasMeter.charge evm.gas OPCODE_JUMP = .ok gas)
    (valid : isValidJumpDest evm.validJumpDestinations destination.toNat = true) :
    jumpStep evm = .ok { evm with
      stack := ⟨rest, by
        have := evm.stack.property
        rw [h, List.length_cons] at this
        omega⟩,
      gas, pc := destination.toNat } := by
  have hstack : evm.stack = ⟨destination :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  simp [jumpStep, popWord, chargeGas, hstack, Stack.pop, paid, valid, bind, Except.bind, pure,
    Except.pure]

/-- JUMPI with a zero condition pays, then goes to the next opcode, whatever the destination. -/
theorem jumpiStep_zero {evm : Evm Meter} {destination : U256} {rest : List U256}
    (h : evm.stack.val = destination :: 0 :: rest) :
    jumpiStep evm = (GasMeter.charge evm.gas OPCODE_JUMPI).map fun gas =>
      { evm with
        stack := ⟨rest, by
          have := evm.stack.property
          rw [h, List.length_cons, List.length_cons] at this
          omega⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨destination :: 0 :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  simp only [jumpiStep, popWord, chargeGas, hstack, Stack.pop]
  rcases hc : GasMeter.charge evm.gas OPCODE_JUMPI with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, advance]

/-- JUMPI with a nonzero condition that pays fails exactly when the destination is not valid. -/
theorem jumpiStep_eq_error_iff {evm : Evm Meter} {destination condition : U256}
    {rest : List U256} {gas : Meter} (h : evm.stack.val = destination :: condition :: rest)
    (nonzero : condition ≠ 0) (paid : GasMeter.charge evm.gas OPCODE_JUMPI = .ok gas) :
    jumpiStep evm = .error .invalidJumpDest ↔
      isValidJumpDest evm.validJumpDestinations destination.toNat = false := by
  have hstack : evm.stack = ⟨destination :: condition :: rest, h ▸ evm.stack.property⟩ :=
    Subtype.ext h
  -- The condition is the word 0 of `BitVec`, as the instruction compares it.
  have nz : ¬condition = 0#256 := nonzero
  simp only [jumpiStep, popWord, chargeGas, hstack, Stack.pop]
  cases hv : isValidJumpDest evm.validJumpDestinations destination.toNat <;>
    simp [paid, hv, nz, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

/-- With the flags of its code, JUMP that pays fails exactly off the JUMPDEST opcodes. -/
theorem jumpStep_eq_error_iff_of_code {evm : Evm Meter} {destination : U256}
    {rest : List U256} {gas : Meter}
    (flags : evm.validJumpDestinations = validJumpDestinations evm.code)
    (h : evm.stack.val = destination :: rest)
    (paid : GasMeter.charge evm.gas OPCODE_JUMP = .ok gas) :
    jumpStep evm = .error .invalidJumpDest ↔
      ¬(destination.toNat ∈ opcodePositions evm.code ∧
        byteAt evm.code destination.toNat = JUMPDEST) := by
  rw [jumpStep_eq_error_iff h paid, flags, ← isValidJumpDest_iff, Bool.not_eq_true]

end EthLib.Execution.Evm
