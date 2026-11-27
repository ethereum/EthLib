module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: rules for the opcodes that read and write only the stack

Each rule here goes from one running frame of a code to the next.

The rules work out the charge of one counter of gas, at every fork.

- An opcode of one, two or three operands puts its result in place of its operands.
  Each such opcode also has a rule of its own, with its byte, its price and its fork.
- POP drops the top word, for 2 gas.
- From Shapella, PUSH0 pushes the word 0, for 2 gas.
- SWAP1 to SWAP16 exchange the top word with the word at their depth, for 3 gas.
- EXP pays its base price and the price per byte of its exponent that the fork sets.

The opcodes that the fork gives an instruction of one, two or three operands run by those rules.

Each rule here is first proved over the steps that also never abort with less gas.

That form gives the rule over the steps from frames that are monotone in gas.

That rule gives the rule over the steps of the logic.

The rule for DUP1 to DUP16 sits with the other rules.

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

/-- A three-operand instruction of the stack, on `x`, `y`, `z`, puts `f x y z` in their place.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem ternaryGA {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256 → U256}
    {x y z : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (ternaryOp cost f)) (hgas : cost ≤ gas) :
    HoareGA fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y z :: rest) memory (gas - cost) state substate
        returnData) := by
  apply At.ruleGA hlt hbyte decoded hrun (runMono_ternaryOp cost f) (noAbort_ternaryOp cost f)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [ternaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩

/-- A three-operand instruction of the stack, on `x`, `y`, `z`, puts `f x y z` in their place.

It holds over the steps from frames that are monotone in gas. -/
theorem ternaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256 → U256}
    {x y z : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (ternaryOp cost f)) (hgas : cost ≤ gas) :
    HoareG fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y z :: rest) memory (gas - cost) state substate
        returnData) :=
  (ternaryGA hlt hbyte decoded hrun hgas).toG

/-- A three-operand instruction of the stack, on `x`, `y`, `z`, puts `f x y z` in their place. -/
theorem ternary {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256 → U256}
    {x y z : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (ternaryOp cost f)) (hgas : cost ≤ gas) :
    Hoare fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (f x y z :: rest) memory (gas - cost) state substate
        returnData) :=
  (ternaryG hlt hbyte decoded hrun hgas).toHoare

/-- POP drops the top word, for 2 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem popGA {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    HoareGA fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 2) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .pop) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) runMono_pop noAbort_pop
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [popStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_POP, BASE], hrun,
    herr, hout, hs, hss, hrd⟩

/-- POP drops the top word, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem popG {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 2) state substate returnData) :=
  (popGA hlt hbyte hgas).toG

/-- POP drops the top word, for 2 gas. -/
theorem pop {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 2) state substate returnData) :=
  (popG hlt hbyte hgas).toHoare

/-- From Shapella, PUSH0 pushes the word 0, for 2 gas, by [EIP-3855][eip-3855].

The stack needs room for one more word.

It holds over the steps from frames that are monotone in gas and never abort with less gas.

[eip-3855]: https://eips.ethereum.org/EIPS/eip-3855#specification
-/
theorem push0GA (hfork : .shapella ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (0 :: stack) memory (gas - 2) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .push 0) rfl (by simpa [Op.since] using hfork))
    (instruction_push 0) (runMono_pushN 0) (noAbort_pushN 0)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [pushN_of_length_lt (by rw [hst]; exact hstack)]
  simp only [Fin.val_zero, ↓reduceIte, OPCODE_PUSH0, BASE]
  rw [charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc],
    by simp [hst, pushData, bufferRead_eq, EthLib.Base.ByteOrder.ofBE_eq_foldl], hmem,
      by simp [hg], hrun, herr,
    hout, hs, hss, hrd⟩

/-- From Shapella, PUSH0 pushes the word 0, for 2 gas, by EIP-3855.

The stack needs room for one more word.

It holds over the steps from frames that are monotone in gas. -/
theorem push0G (hfork : .shapella ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (0 :: stack) memory (gas - 2) state substate returnData) :=
  (push0GA hfork hlt hbyte hgas hstack).toG

/-- From Shapella, PUSH0 pushes the word 0, for 2 gas, by EIP-3855.

The stack needs room for one more word. -/
theorem push0 (hfork : .shapella ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (0 :: stack) memory (gas - 2) state substate returnData) :=
  (push0G hfork hlt hbyte hgas hstack).toHoare

/-- SWAP(n + 1), for the `n` that the byte at the program counter decodes to.

It exchanges the top word with the word `x` at depth `n + 1`, for 3 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem swap_of_decodeGA {byte : UInt8} {n : Fin 16} {top x : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.swap n))
    (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareGA fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) (runMono_swapN n) (noAbort_swapN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [swapN_of_getElem? hst hx, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem,
    by simp [hg, OPCODE_SWAP, VERY_LOW], hrun, herr, hout, hs, hss, hrd⟩

/-- SWAP(n + 1), for the `n` that the byte at the program counter decodes to.

It exchanges the top word with the word `x` at depth `n + 1`, for 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem swap_of_decodeG {byte : UInt8} {n : Fin 16} {top x : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.swap n))
    (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  (swap_of_decodeGA hlt hbyte decoded hx hgas).toG

/-- SWAP(n + 1), for the `n` that the byte at the program counter decodes to.

It exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swap_of_decode {byte : UInt8} {n : Fin 16} {top x : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.swap n))
    (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  (swap_of_decodeG hlt hbyte decoded hx hgas).toHoare

/-- SWAP(n + 1) exchanges the top word with the word `x` at depth `n + 1`, for 3 gas.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem swapGA (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareGA fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  swap_of_decodeGA hlt hbyte (decode_swap n) hx hgas

/-- SWAP(n + 1) exchanges the top word with the word `x` at depth `n + 1`, for 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem swapG (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  (swapGA n hlt hbyte hx hgas).toG

/-- SWAP(n + 1) exchanges the top word with the word `x` at depth `n + 1`, for 3 gas. -/
theorem swap (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (top :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate
        returnData) :=
  (swapG n hlt hbyte hx hgas).toHoare

/-- EXP puts `base` to the power `exponent` in place of both.

It pays 10 and the price per byte of the exponent that the fork sets.

It holds over the steps from frames that are monotone in gas and never abort with less gas. -/
theorem expGA {base exponent : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x0a)
    (hgas : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent ≤
      gas) :
    HoareGA fork
      (At code message pc (base :: exponent :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
          exponentBytes exponent)) state substate returnData) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .exp) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) runMono_exp noAbort_exp
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [expStep_of_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩

/-- EXP puts `base` to the power `exponent` in place of both.

It pays 10 and the price per byte of the exponent that the fork sets.

It holds over the steps from frames that are monotone in gas. -/
theorem expG {base exponent : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x0a)
    (hgas : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent ≤
      gas) :
    HoareG fork (At code message pc (base :: exponent :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
          exponentBytes exponent)) state substate returnData) :=
  (expGA hlt hbyte hgas).toG

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

/-! ## One rule for each opcode of one, two or three operands -/

section Operands

variable {x y z : U256} {rest : List U256}

/-- ADD replaces `x` and `y` with the sum of `x` and `y` modulo `2^256`.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem add_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x01) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (add x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .add) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- ADD replaces `x` and `y` with the sum of `x` and `y` modulo `2^256`.

It costs 3 gas. -/
theorem add_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x01) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (add x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (add_ruleG hlt hbyte hgas).toHoare

/-- MUL replaces `x` and `y` with the product of `x` and `y` modulo `2^256`.

It costs 5 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem mul_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x02) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (mul x y :: rest) memory (gas - 5) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .mul) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- MUL replaces `x` and `y` with the product of `x` and `y` modulo `2^256`.

It costs 5 gas. -/
theorem mul_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x02) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (mul x y :: rest) memory (gas - 5) state
        substate returnData) :=
  (mul_ruleG hlt hbyte hgas).toHoare

/-- SUB replaces `x` and `y` with `x` minus `y` modulo `2^256`.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem sub_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x03) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (sub x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .sub) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- SUB replaces `x` and `y` with `x` minus `y` modulo `2^256`.

It costs 3 gas. -/
theorem sub_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x03) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (sub x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (sub_ruleG hlt hbyte hgas).toHoare

/-- DIV replaces `x` and `y` with the quotient of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem div_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x04) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (div x y :: rest) memory (gas - 5) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .div) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- DIV replaces `x` and `y` with the quotient of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas. -/
theorem div_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x04) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (div x y :: rest) memory (gas - 5) state
        substate returnData) :=
  (div_ruleG hlt hbyte hgas).toHoare

/-- SDIV replaces `x` and `y` with the signed quotient of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem sdiv_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x05) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (sdiv x y :: rest) memory (gas - 5) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .sdiv) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- SDIV replaces `x` and `y` with the signed quotient of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas. -/
theorem sdiv_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x05) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (sdiv x y :: rest) memory (gas - 5) state
        substate returnData) :=
  (sdiv_ruleG hlt hbyte hgas).toHoare

/-- MOD replaces `x` and `y` with the remainder of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem mod_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x06) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (mod x y :: rest) memory (gas - 5) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .mod) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- MOD replaces `x` and `y` with the remainder of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas. -/
theorem mod_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x06) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (mod x y :: rest) memory (gas - 5) state
        substate returnData) :=
  (mod_ruleG hlt hbyte hgas).toHoare

/-- SMOD replaces `x` and `y` with the signed remainder of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem smod_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x07) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (smod x y :: rest) memory (gas - 5) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .smod) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- SMOD replaces `x` and `y` with the signed remainder of `x` by `y`, or 0 when `y` is 0.

It costs 5 gas. -/
theorem smod_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x07) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (smod x y :: rest) memory (gas - 5) state
        substate returnData) :=
  (smod_ruleG hlt hbyte hgas).toHoare

/-- ADDMOD replaces `x`, `y` and `z` with the sum of `x` and `y` modulo `z`, or 0 when `z` is 0.

It costs 8 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem addmod_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x08) (hgas : 8 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (addmod x y z :: rest) memory (gas - 8) state
        substate returnData) :=
  ternaryG hlt hbyte (ofByte_of_decode (op := .addmod) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- ADDMOD replaces `x`, `y` and `z` with the sum of `x` and `y` modulo `z`, or 0 when `z` is 0.

It costs 8 gas. -/
theorem addmod_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x08) (hgas : 8 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (addmod x y z :: rest) memory (gas - 8) state
        substate returnData) :=
  (addmod_ruleG hlt hbyte hgas).toHoare

/-- MULMOD replaces `x`, `y` and `z` with the product of `x` and `y` modulo `z`, or 0 when `z` is 0.

It costs 8 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem mulmod_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x09) (hgas : 8 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (mulmod x y z :: rest) memory (gas - 8) state
        substate returnData) :=
  ternaryG hlt hbyte (ofByte_of_decode (op := .mulmod) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- MULMOD replaces `x`, `y` and `z` with the product of `x` and `y` modulo `z`, or 0 when `z` is 0.

It costs 8 gas. -/
theorem mulmod_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x09) (hgas : 8 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: z :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (mulmod x y z :: rest) memory (gas - 8) state
        substate returnData) :=
  (mulmod_ruleG hlt hbyte hgas).toHoare

/-- SIGNEXTEND replaces `x` and `y` with `y` sign-extended from its byte `x`.

It counts the bytes from the least significant one.

It costs 5 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem signextend_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x0b) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (signextend x y :: rest) memory (gas - 5) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .signextend) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- SIGNEXTEND replaces `x` and `y` with `y` sign-extended from its byte `x`.

It counts the bytes from the least significant one.

It costs 5 gas. -/
theorem signextend_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x0b) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (signextend x y :: rest) memory (gas - 5) state
        substate returnData) :=
  (signextend_ruleG hlt hbyte hgas).toHoare

/-- LT replaces `x` and `y` with 1 when `x < y` as unsigned words, and 0 otherwise.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem lt_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x10) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (lessThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .lt) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- LT replaces `x` and `y` with 1 when `x < y` as unsigned words, and 0 otherwise.

It costs 3 gas. -/
theorem lt_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x10) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (lessThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (lt_ruleG hlt hbyte hgas).toHoare

/-- GT replaces `x` and `y` with 1 when `x > y` as unsigned words, and 0 otherwise.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem gt_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x11) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (greaterThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .gt) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- GT replaces `x` and `y` with 1 when `x > y` as unsigned words, and 0 otherwise.

It costs 3 gas. -/
theorem gt_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x11) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (greaterThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (gt_ruleG hlt hbyte hgas).toHoare

/-- SLT replaces `x` and `y` with 1 when `x < y` as signed words, and 0 otherwise.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem slt_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x12) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (signedLessThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .slt) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- SLT replaces `x` and `y` with 1 when `x < y` as signed words, and 0 otherwise.

It costs 3 gas. -/
theorem slt_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x12) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (signedLessThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (slt_ruleG hlt hbyte hgas).toHoare

/-- SGT replaces `x` and `y` with 1 when `x > y` as signed words, and 0 otherwise.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem sgt_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x13) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (signedGreaterThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .sgt) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- SGT replaces `x` and `y` with 1 when `x > y` as signed words, and 0 otherwise.

It costs 3 gas. -/
theorem sgt_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x13) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (signedGreaterThan x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (sgt_ruleG hlt hbyte hgas).toHoare

/-- EQ replaces `x` and `y` with 1 when `x = y`, and 0 otherwise.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem eq_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x14) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (equal x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .eq) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- EQ replaces `x` and `y` with 1 when `x = y`, and 0 otherwise.

It costs 3 gas. -/
theorem eq_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x14) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (equal x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (eq_ruleG hlt hbyte hgas).toHoare

/-- ISZERO replaces `x` with 1 when `x` is 0, and 0 otherwise.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem iszero_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x15) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (isZero x :: rest) memory (gas - 3) state
        substate returnData) :=
  unaryG hlt hbyte (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- ISZERO replaces `x` with 1 when `x` is 0, and 0 otherwise.

It costs 3 gas. -/
theorem iszero_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x15) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (isZero x :: rest) memory (gas - 3) state
        substate returnData) :=
  (iszero_ruleG hlt hbyte hgas).toHoare

/-- AND replaces `x` and `y` with the bitwise and of `x` and `y`.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem and_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x16) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseAnd x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .and) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- AND replaces `x` and `y` with the bitwise and of `x` and `y`.

It costs 3 gas. -/
theorem and_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x16) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseAnd x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (and_ruleG hlt hbyte hgas).toHoare

/-- OR replaces `x` and `y` with the bitwise or of `x` and `y`.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem or_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x17) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseOr x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .or) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- OR replaces `x` and `y` with the bitwise or of `x` and `y`.

It costs 3 gas. -/
theorem or_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x17) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseOr x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (or_ruleG hlt hbyte hgas).toHoare

/-- XOR replaces `x` and `y` with the bitwise exclusive or of `x` and `y`.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem xor_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x18) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseXor x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .xor) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- XOR replaces `x` and `y` with the bitwise exclusive or of `x` and `y`.

It costs 3 gas. -/
theorem xor_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x18) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseXor x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (xor_ruleG hlt hbyte hgas).toHoare

/-- NOT replaces `x` with the bitwise complement of `x`.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem not_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x19) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseNot x :: rest) memory (gas - 3) state
        substate returnData) :=
  unaryG hlt hbyte (ofByte_of_decode (op := .not) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- NOT replaces `x` with the bitwise complement of `x`.

It costs 3 gas. -/
theorem not_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x19) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseNot x :: rest) memory (gas - 3) state
        substate returnData) :=
  (not_ruleG hlt hbyte hgas).toHoare

/-- BYTE replaces `x` and `y` with byte `x` of `y`, counting from the most significant byte.

It gives 0 when `x` is 32 or more.

It costs 3 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem byte_ruleG
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1a) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (getByte x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .byte) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) hgas

/-- BYTE replaces `x` and `y` with byte `x` of `y`, counting from the most significant byte.

It gives 0 when `x` is 32 or more.

It costs 3 gas. -/
theorem byte_rule
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1a) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (getByte x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (byte_ruleG hlt hbyte hgas).toHoare

/-- From Constantinople, SHL replaces `x` and `y` with `y` shifted left by `x` bits.

It costs 3 gas, by EIP-145.

It holds over the steps from frames that are monotone in gas. -/
theorem shl_ruleG
    (hfork : .constantinople ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1b) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseShl x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .shl) rfl hfork)
    (instruction_of_stackOnlyStep rfl) hgas

/-- From Constantinople, SHL replaces `x` and `y` with `y` shifted left by `x` bits.

It costs 3 gas, by EIP-145. -/
theorem shl_rule
    (hfork : .constantinople ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1b) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseShl x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (shl_ruleG hfork hlt hbyte hgas).toHoare

/-- From Constantinople, SHR replaces `x` and `y` with `y` shifted right by `x` bits.

It costs 3 gas, by EIP-145.

It holds over the steps from frames that are monotone in gas. -/
theorem shr_ruleG
    (hfork : .constantinople ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1c) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseShr x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .shr) rfl hfork)
    (instruction_of_stackOnlyStep rfl) hgas

/-- From Constantinople, SHR replaces `x` and `y` with `y` shifted right by `x` bits.

It costs 3 gas, by EIP-145. -/
theorem shr_rule
    (hfork : .constantinople ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1c) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseShr x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (shr_ruleG hfork hlt hbyte hgas).toHoare

/-- From Constantinople, SAR replaces `x` and `y` with the signed right shift of `y` by `x` bits.

It costs 3 gas, by EIP-145.

It holds over the steps from frames that are monotone in gas. -/
theorem sar_ruleG
    (hfork : .constantinople ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1d) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseSar x y :: rest) memory (gas - 3) state
        substate returnData) :=
  binaryG hlt hbyte (ofByte_of_decode (op := .sar) rfl hfork)
    (instruction_of_stackOnlyStep rfl) hgas

/-- From Constantinople, SAR replaces `x` and `y` with the signed right shift of `y` by `x` bits.

It costs 3 gas, by EIP-145. -/
theorem sar_rule
    (hfork : .constantinople ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1d) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (x :: y :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (bitwiseSar x y :: rest) memory (gas - 3) state
        substate returnData) :=
  (sar_ruleG hfork hlt hbyte hgas).toHoare

/-- From Fusaka, CLZ replaces `x` with the number of leading zero bits of `x`.

It costs 5 gas, by EIP-7939.

It holds over the steps from frames that are monotone in gas. -/
theorem clz_ruleG
    (hfork : .fusaka ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1e) (hgas : 5 ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (countLeadingZeros x :: rest) memory (gas - 5) state
        substate returnData) :=
  unaryG hlt hbyte (ofByte_of_decode (op := .clz) rfl hfork)
    (instruction_of_stackOnlyStep rfl) hgas

/-- From Fusaka, CLZ replaces `x` with the number of leading zero bits of `x`.

It costs 5 gas, by EIP-7939. -/
theorem clz_rule
    (hfork : .fusaka ≤ fork)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x1e) (hgas : 5 ≤ gas) :
    Hoare fork (At code message pc (x :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (countLeadingZeros x :: rest) memory (gas - 5) state
        substate returnData) :=
  (clz_ruleG hfork hlt hbyte hgas).toHoare

end Operands

end EthLib.Execution.Evm.Logic
