module

public import EthLib.Execution.Proofs.Evm.Logic.Fault

/-!
# Proofs: a contract that rejects a call that sends value

This example shows a check on a word that the frame reads from its message.

The bytecode `0x3415600657fe5b600080f3` reads the value that the message sends.

If the value is zero, it returns with no output; otherwise it runs the byte `0xfe`.

- At 0, `34 15` pushes 1 when the value is zero, and 0 otherwise.
- At 2, `60 06 57` jumps to 6 when that word is not zero.
- At 5, `fe` is no opcode, so the frame halts exceptionally.
- At 6, `5b` marks the destination of the jump.
- At 7, `60 00 80 f3` returns the 0 bytes of memory at offset 0.

The run that returns costs 25 gas.

The run that halts takes all the gas of the frame, and keeps its state and substate.

The rules are those of one counter of gas, the meter of every fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.NoValue

open EthLib.Base (Fork U256)

variable {fork : Fork}

/-! ## The code -/

/-- The bytecode as one number, whose highest byte is the first byte of the code. -/
def CODE_NAT : Nat := 0x3415600657fe5b600080f3

/-- The bytecode of the contract: the 11 bytes of its number. -/
@[irreducible] def CODE : ByteArray := NatCode.ofNat CODE_NAT 11

/-- The equation of the code, which proofs rewrite by. -/
theorem CODE_eq : CODE = NatCode.ofNat CODE_NAT 11 := by
  unfold CODE
  rfl

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- A call that sends no value returns with no output, for 25 gas. -/
theorem spec_zero (hvalue : message.value = 0) {gas : Nat} (hgas : 25 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - 25) state substate) := by
  have hz : isZero message.value ≠ 0 := by rw [isZero, ite_eq_left hvalue]; decide
  iterate 7 evm_step [CODE_eq, CODE_NAT]
  -- A range of size 0 does not grow memory.
  have hm : extendMemory ByteArray.empty.size [(0#256, 0#256)] = ⟨0, 0⟩ := by decide
  refine Spec.consequence (Logic.«return» (by evm_code [CODE_eq, CODE_NAT])
    (by evm_code [CODE_eq, CODE_NAT]) (by rw [hm]; exact Nat.zero_le _)) (fun _ x => x)
    fun evm ⟨hr, he, ho, hg, hs, hss⟩ => ⟨hr, he, by simpa [hm, memoryReadBytes] using ho, by
      rw [hm] at hg
      simpa using hg, hs, hss⟩

/-- A call that sends value halts exceptionally at the byte `0xfe`.

It needs 18 gas to get there, and then holds no gas. -/
theorem spec_nonzero (hvalue : message.value ≠ 0) {gas : Nat} (hgas : 18 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have hz : isZero message.value = 0 := ite_eq_right hvalue
  iterate 4 evm_step [CODE_eq, CODE_NAT]
  evm_fault [CODE_eq, CODE_NAT]

end EthLib.Execution.Evm.Logic.NoValue
