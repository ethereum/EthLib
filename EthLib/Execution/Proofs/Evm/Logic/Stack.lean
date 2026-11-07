module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: rules for the opcodes that read and write only the stack

Each opcode of the stack has a rule, from one running frame of a code to the next.

A one-operand, two-operand or three-operand opcode puts its result in place of its operands.

The opcodes that the fork gives such an instruction run by the rules for one, two or three operands.

POP drops the top word, for 2 gas.

The rule for DUP1 to DUP16 sits with the other rules, and pushes a copy of the word at a depth.

SWAP1 to SWAP16 exchange the top word with the word at their depth.

Each SWAP costs 3 gas.

EXP pays its base price and the price per byte of its exponent that the fork sets.

The rules work out the charge of one counter of gas, at every fork.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- An opcode that reads and writes only the stack runs its instruction of the stack. -/
theorem instruction_of_stackOnlyStep {Meter : Type} [GasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : stackOnlyStep fork op = some run) : instruction fork op = some run := by
  simp [instruction, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- The byte `0x90 + n` decodes as SWAP(n + 1). -/
theorem decode_swap (n : Fin 16) : Op.decode (0x90 + n.val).toUInt8 = some (.swap n) := by
  revert n
  decide

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- A three-operand instruction of the stack, on `x`, `y`, `z`, puts `f x y z` in their place. -/
theorem ternary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256 → U256}
    {x y z : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (ternaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: y :: z :: rest) memory gas state substate)
      (At code message (pc + 1) (f x y z :: rest) memory (gas - cost) state substate) := by
  apply At.rule hlt hbyte decoded hrun
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [ternaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hs, hss⟩

/-- POP drops the top word, for 2 gas. -/
theorem pop {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 2) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .pop) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [popStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_POP, BASE], hrun,
    herr, hs, hss⟩

/-- SWAP(n + 1) exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swap (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (top :: rest) memory gas state substate)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (decode_swap n) (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [swapN_of_getElem? hst hx, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem,
    by simp [hg, OPCODE_SWAP, VERY_LOW], hrun, herr, hs, hss⟩

/-- EXP puts `base` to the power `exponent` in place of both.

It pays 10 and the price per byte of the exponent that the fork sets. -/
theorem exp {base exponent : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x0a)
    (hgas : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent ≤
      gas) :
    Hoare fork (At code message pc (base :: exponent :: rest) memory gas state substate)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
          exponentBytes exponent)) state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .exp) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  rw [expStep_of_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hs, hss⟩

end EthLib.Execution.Evm.Logic
