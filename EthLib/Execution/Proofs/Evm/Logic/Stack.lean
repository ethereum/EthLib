module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: rules for the opcodes that read and write only the stack

Each rule here goes from one running frame of a code to the next.

A one-operand, two-operand or three-operand opcode puts its result in place of its operands.

The opcodes that the fork gives such an instruction run by the rules for one, two or three operands.

POP drops the top word, for 2 gas.

The rule for DUP1 to DUP16 sits with the other rules, and pushes a copy of the word at a depth.

SWAP1 to SWAP16 exchange the top word with the word at their depth.

Each SWAP costs 3 gas.

EXP pays its base price and the price per byte of its exponent that the fork sets.

Each rule here is first proved over the steps from frames that are monotone in gas.

The rule over the steps of the logic then follows from that form.

The rules work out the charge of one counter of gas, at every fork.

DUPN, SWAPN and EXCHANGE of Glamsterdam have no rule yet.
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
  {returnData : ByteArray}

/-- A three-operand instruction of the stack, on `x`, `y`, `z`, puts `f x y z` in their place. -/
theorem ternaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256 → U256}
    {x y z : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (ternaryOp cost f)) (hgas : cost ≤ gas) :
    HoareG fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y z :: rest) memory (gas - cost) state substate
        returnData) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_ternaryOp cost f)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [ternaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩

/-- A three-operand instruction of the stack, on `x`, `y`, `z`, puts `f x y z` in their place. -/
theorem ternary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256 → U256}
    {x y z : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (ternaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y z :: rest) memory (gas - cost) state substate
        returnData) :=
  (ternaryG hlt hbyte decoded hrun hgas).toHoare

/-- POP drops the top word, for 2 gas. -/
theorem popG {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 2) state substate returnData) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .pop) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) runMono_pop
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [popStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_POP, BASE], hrun,
    herr, hout, hs, hss, hrd⟩

/-- POP drops the top word, for 2 gas. -/
theorem pop {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 2) state substate returnData) :=
  (popG hlt hbyte hgas).toHoare

/-- SWAP(n + 1), for the `n` that the byte at the program counter decodes to.

It exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swap_of_decodeG {byte : UInt8} {n : Fin 16} {top x : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.swap n))
    (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) (runMono_swapN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [swapN_of_getElem? hst hx, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem,
    by simp [hg, OPCODE_SWAP, VERY_LOW], hrun, herr, hout, hs, hss, hrd⟩

/-- SWAP(n + 1), for the `n` that the byte at the program counter decodes to.

It exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swap_of_decode {byte : UInt8} {n : Fin 16} {top x : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.swap n))
    (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  (swap_of_decodeG hlt hbyte decoded hx hgas).toHoare

/-- SWAP(n + 1) exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swapG (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  swap_of_decodeG hlt hbyte (decode_swap n) hx hgas

/-- SWAP(n + 1) exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swap (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  swap_of_decode hlt hbyte (decode_swap n) hx hgas

/-- EXP puts `base` to the power `exponent` in place of both.

It pays 10 and the price per byte of the exponent that the fork sets. -/
theorem expG {base exponent : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x0a)
    (hgas : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent ≤
      gas) :
    HoareG fork (At code message pc (base :: exponent :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
          exponentBytes exponent)) state substate returnData) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .exp) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) runMono_exp
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [expStep_of_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩

/-- EXP puts `base` to the power `exponent` in place of both.

It pays 10 and the price per byte of the exponent that the fork sets. -/
theorem exp {base exponent : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x0a)
    (hgas : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent ≤
      gas) :
    Hoare fork (At code message pc (base :: exponent :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
          exponentBytes exponent)) state substate returnData) :=
  (expG hlt hbyte hgas).toHoare

end EthLib.Execution.Evm.Logic
