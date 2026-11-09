module

public import EthLib.Execution.Proofs.Evm.Logic.Steps
public import EthLib.Execution.Proofs.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Logic.GasMono

/-!
# Proofs: frames that halt exceptionally

A step that fails halts the frame exceptionally, unless its error aborts the whole run.

The halted frame has no output, holds the error, and keeps the state and substate it had.

It holds no gas: the meter of one counter of gas is exhausted to 0, at every fork with that meter.

The frame does not roll back the state itself.

The caller discards the state of a frame that halts exceptionally.

No statement here says so.

The rules here cover a byte that is no opcode at the fork, such as `0xfe` at every fork.

They also cover JUMP, and JUMPI on a nonzero condition, to an invalid jump destination.

A tactic closes such a step in a code stored as one number.

It proves a destination invalid when the byte there is not JUMPDEST.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- A frame that halted exceptionally with `error`, with no output and no gas left.

It holds the state and the substate that its frame had when it halted. -/
def Faulted (error : EvmError) (state : State.TransactionState) (substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  evm.running = false ∧ evm.error = some error ∧ evm.output = .empty ∧ evm.gas = 0 ∧
    evm.state = state ∧ evm.substate = substate

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A frame whose step fails with an error that does not abort halts with that error. -/
theorem At.fault {e : EvmError} (halts : e.aborts = false)
    (h : ∀ evm, At code message pc stack memory gas state substate returnData evm →
      step fork evm = .error e) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (Faulted e state substate) := by
  apply Triple.of_step
  intro evm hat
  obtain ⟨-, -, -, -, -, -, -, hrun, -, -, hs, hss, -⟩ := id hat
  exact ⟨_, Step.halt hrun (h evm hat) halts, rfl, rfl, rfl, rfl, rfl, hs, hss⟩

/-- A byte that is no opcode at the fork halts the frame with that byte as an invalid opcode.

The step is monotone in gas, since it fails with any gas. -/
theorem invalidG {byte : UInt8} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (none : Op.ofByte fork byte = none) :
    SpecG fork (At code message pc stack memory gas state substate returnData)
      (Faulted (.invalidOpcode byte) state substate) := by
  apply Triple.of_step
  intro evm hat
  obtain ⟨hcode, -, -, hpc, -, -, -, hrun, -, -, hs, hss, -⟩ := hat
  subst hcode hpc
  have hnone : Op.ofByte fork evm.code[evm.pc] = .none := by rw [hbyte]; exact none
  have hstep : step fork evm = .error (.invalidOpcode byte) := by
    rw [step_of_ofByte_eq_none hlt hnone, hbyte]
  exact ⟨_, ⟨Step.halt hrun hstep rfl, gasMono_of_none hlt hnone⟩,
    rfl, rfl, rfl, rfl, rfl, hs, hss⟩

/-- A byte that is no opcode at the fork halts the frame with that byte as an invalid opcode. -/
theorem invalid {byte : UInt8} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (none : Op.ofByte fork byte = none) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (Faulted (.invalidOpcode byte) state substate) :=
  (invalidG hlt hbyte none).toSpec

/-- The byte `0xfe` is no opcode at any fork, so it halts the frame as an invalid opcode. -/
theorem invalid_fe (hlt : pc < code.size) (hbyte : code[pc] = 0xfe) :
    Spec fork (At code message pc stack memory gas state substate returnData)
      (Faulted (.invalidOpcode 0xfe) state substate) :=
  invalid hlt hbyte rfl

/-- JUMP, with 8 gas, halts the frame at a position that is not a valid jump destination. -/
theorem jump_invalid {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas)
    (invalid : isValidJumpDest (validJumpDestinations code) destination.toNat = false) :
    Spec fork (At code message pc (destination :: rest) memory gas state substate returnData)
      (Faulted .invalidJumpDest state substate) := by
  refine At.fault rfl fun evm ⟨hcode, hj, _, hpc, hst, _, hg, _⟩ => ?_
  subst hcode hpc
  have decoded : Op.ofByte fork evm.code[evm.pc] = some .jump := by
    rw [hbyte]
    exact ofByte_of_decode rfl (Fork.frontier_le _)
  rw [step_of_instruction hlt decoded instruction_jump,
    (jumpStep_eq_error_iff hst (charge_nat (by rw [hg]; exact hgas))).mpr
      (by rw [hj]; exact invalid)]
  rfl

/-- JUMPI on a nonzero condition, with 10 gas, halts the frame at an invalid destination. -/
theorem jumpi_invalid {destination condition : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (nonzero : condition ≠ 0)
    (invalid : isValidJumpDest (validJumpDestinations code) destination.toNat = false) :
    Spec fork (At code message pc (destination :: condition :: rest) memory gas state substate
        returnData)
      (Faulted .invalidJumpDest state substate) := by
  refine At.fault rfl fun evm ⟨hcode, hj, _, hpc, hst, _, hg, _⟩ => ?_
  subst hcode hpc
  have decoded : Op.ofByte fork evm.code[evm.pc] = some .jumpi := by
    rw [hbyte]
    exact ofByte_of_decode rfl (Fork.frontier_le _)
  rw [step_of_instruction hlt decoded instruction_jumpi,
    (jumpiStep_eq_error_iff hst nonzero (charge_nat (by rw [hg]; exact hgas))).mpr
      (by rw [hj]; exact invalid)]
  rfl

open Lean.Parser.Tactic

/-- Proves that a destination is not a valid jump destination, as its byte is not JUMPDEST. -/
syntax "evm_bad_dest" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_bad_dest [$ls,*]) => `(tactic|
      (simp only [$ls,*, BitVec.reduceToNat]
       refine NatCode.not_valid_of_natByte ?byte
       case byte => decide))

/-- Closes a specification at an opcode that halts the frame exceptionally.

The opcode is a byte that is no opcode at the fork, or a jump to an invalid destination.

The rewrite rules `ls` turn the facts about the code into facts about numbers. -/
syntax "evm_fault" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| evm_fault [$ls,*]) => `(tactic| first
      | (refine' invalid ?lt ?op ?none
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case none => rfl)
      | (refine' jump_invalid ?lt ?op ?gas ?bad
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case bad => evm_bad_dest [$ls,*])
      | (refine' jumpi_invalid ?lt ?op ?gas ?nz ?bad
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => evm_gas
         case nz => first | assumption | decide
         case bad => evm_bad_dest [$ls,*])
      | fail "no rule of an exceptional halt applies to the opcode at the program counter")

end EthLib.Execution.Evm.Logic
