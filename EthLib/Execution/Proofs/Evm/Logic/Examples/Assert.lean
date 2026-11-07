module

public import EthLib.Execution.Proofs.Evm.Logic.Fault

/-!
# Proofs: a contract that asserts that its call data is nonzero

This example shows a frame that halts exceptionally on a failed check.

The bytecode `0x600035600757fe5b600080f3` reads the first word of its call data.

If the word is not zero, it returns with no output; otherwise it runs the byte `0xfe`.

- At 0, `60 00 35` reads the word of call data at offset 0.
- At 3, `60 07 57` jumps to 7 when the word is not zero.
- At 6, `fe` is no opcode, so the frame halts exceptionally.
- At 7, `5b` marks the destination of the jump.
- At 8, `60 00 80 f3` returns the 0 bytes of memory at offset 0.

The run that returns costs 26 gas.

The run that halts takes all the gas of the frame, and keeps its state and substate.

The rules are those of one counter of gas, the meter of every fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Assert

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-! ## The code -/

/-- The bytecode as one number, whose highest byte is the first byte of the code. -/
def CODE_NAT : Nat := 0x600035600757fe5b600080f3

/-- The bytecode of the contract: the 12 bytes of its number. -/
@[irreducible] def CODE : ByteArray := NatCode.ofNat CODE_NAT 12

/-- The equation of the code, which proofs rewrite by. -/
theorem CODE_eq : CODE = NatCode.ofNat CODE_NAT 12 := by
  unfold CODE
  rfl

/-- The word that the code checks: the first word of its call data. -/
def word (data : ByteArray) : U256 := loadWord data 0 32

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- A call whose first word is not zero returns with no output, for 26 gas. -/
theorem spec_nonzero (hword : word message.data ≠ 0) {gas : Nat} (hgas : 26 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - 26) state substate) := by
  iterate 3 evm_step [CODE_eq, CODE_NAT]
  refine Triple.seq (jumpi_taken (by evm_code [CODE_eq, CODE_NAT])
    (by evm_code [CODE_eq, CODE_NAT]) (by omega) hword (by evm_dest [CODE_eq, CODE_NAT])) ?_
  evm_tidy
  iterate 3 evm_step [CODE_eq, CODE_NAT]
  -- A range of size 0 does not grow memory.
  have hz : extendMemory ByteArray.empty.size [(0#256, 0#256)] = ⟨0, 0⟩ := by decide
  refine Spec.consequence (Logic.«return» (by evm_code [CODE_eq, CODE_NAT])
    (by evm_code [CODE_eq, CODE_NAT]) (by rw [hz]; exact Nat.zero_le _)) (fun _ x => x)
    fun evm ⟨hr, he, ho, hg, hs, hss⟩ => ⟨hr, he, by simpa [hz, memoryReadBytes] using ho, by
      rw [hz] at hg
      simpa using hg, hs, hss⟩

/-- A call whose first word is zero halts exceptionally at the byte `0xfe`.

It needs 19 gas to get there, and then holds no gas. -/
theorem spec_zero (hword : word message.data = 0) {gas : Nat} (hgas : 19 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  iterate 3 evm_step [CODE_eq, CODE_NAT]
  rw [show loadWord message.data 0 32 = 0 from hword]
  evm_step [CODE_eq, CODE_NAT]
  evm_fault [CODE_eq, CODE_NAT]

/-- The loop of the interpreter runs a call whose first word is not zero to its return. -/
theorem runFrame_nonzero (hword : word message.data ≠ 0) {gas : Nat} (hgas : 26 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Halted false .empty (gas - 26) state substate stopped :=
  (spec_nonzero hword hgas).runFrame start within

/-- The loop of the interpreter runs a call whose first word is zero to an exceptional halt. -/
theorem runFrame_zero (hword : word message.data = 0) {gas : Nat} (hgas : 19 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Faulted (.invalidOpcode 0xfe) state substate stopped :=
  (spec_zero hword hgas).runFrame start within

end EthLib.Execution.Evm.Logic.Assert
