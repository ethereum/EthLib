module

public import EthLib.Execution.Evm.Instructions.StackOnly
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Instructions.StackN
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.StackOnly`

PUSH reads the code past its end as zeros.

POP on a stack with a word on top pays its price.

Then it drops that word and moves the program counter by 1.

PUSH0 to PUSH32 on a stack with room pay the price of PUSH0 for width 0, else of PUSH.

Then they push the next `n` bytes of code, as a big-endian word.

They move the program counter by `1 + n`.

DUP and SWAP fail with an underflow exactly on a stack too short for their depth.

From Spurious Dragon, EXP costs 10 plus 50 per byte of the exponent.

KECCAK256 pays 30, 6 per hashed word and the growth of memory.

None of these instructions changes the message, the state or the substate of the frame.

Each of them keeps the size of memory a multiple of 32.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 byteAt_append_zeros)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- PUSH reads the code past its end as zeros, so zeros appended to the code change nothing. -/
theorem pushData_append_zeros (code : ByteArray) (pc n k : Nat) :
    pushData (code ++ ByteArray.mk (Array.replicate k 0)) pc n = pushData code pc n := by
  simp only [pushData, bufferRead, byteAt_append_zeros]

/-- DUP(n + 1) that pays fails with an underflow on a stack of at most `n` words. -/
theorem dupN_of_length_le {n : Fin 16} {evm : Evm fork Meter} {gas : Meter}
    (paid : GasMeter.charge evm.gas OPCODE_DUP = .ok gas) (h : evm.stack.val.length ≤ n) :
    dupN n evm = .error .stackUnderflow := by
  simp [dupN, chargeGas, paid, bind, Except.bind, pure, Except.pure,
    List.getElem?_eq_none_iff.mpr h]

/-- DUP(n + 1) on a stack with `x` at depth `n` and room for one more word: pay, then push `x`. -/
theorem dupN_of_getElem? {n : Fin 16} {evm : Evm fork Meter} {x : U256}
    (h : evm.stack.val[n.val]? = some x) (room : evm.stack.val.length < STACK_LIMIT) :
    dupN n evm = (GasMeter.charge evm.gas OPCODE_DUP).map fun gas =>
      { evm with stack := ⟨x :: evm.stack.val, room⟩, gas, pc := evm.pc + 1 } := by
  have full : ¬evm.stack.val.length = STACK_LIMIT := Nat.ne_of_lt room
  rcases hc : GasMeter.charge evm.gas OPCODE_DUP with _ | _ <;>
    simp [hc, dupN, chargeGas, bind, Except.bind, pure, Except.pure, Except.map, h, pushWord,
      Stack.push, full, advance]

/-- SWAP(n + 1) that pays fails with an underflow on a stack of at most `n + 1` words. -/
theorem swapN_of_length_le {n : Fin 16} {evm : Evm fork Meter} {gas : Meter}
    (paid : GasMeter.charge evm.gas OPCODE_SWAP = .ok gas) (h : evm.stack.val.length ≤ n + 1) :
    swapN n evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | ⟨top, rest⟩, _⟩
  · simp [swapN, chargeGas, paid, bind, Except.bind, pure, Except.pure, hs]
  · rw [hs] at h
    simp only [List.length_cons] at h
    simp [swapN, chargeGas, paid, bind, Except.bind, pure, Except.pure, hs,
      List.getElem?_eq_none_iff.mpr (show rest.length ≤ n.val by omega)]

/-- POP on a stack with `x` on top: pay, then drop `x`. -/
theorem popStep_cons {evm : Evm fork Meter} {x : U256} {rest : List U256}
    (h : evm.stack.val = x :: rest) :
    popStep evm = (GasMeter.charge evm.gas OPCODE_POP).map fun gas =>
      { evm with
        stack := ⟨rest, by
          have := evm.stack.property
          rw [h, List.length_cons] at this
          omega⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨x :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  simp only [popStep, popWord, chargeGas, hstack, Stack.pop]
  rcases hc : GasMeter.charge evm.gas OPCODE_POP with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, advance]

/-- PUSHn, for each width from 0 to 32, on a stack with room: pay, then push the next `n` bytes.

PUSH0 pays the price of PUSH0, and the other widths the price of PUSH.

The program counter moves past the opcode and its `n` bytes. -/
theorem pushN_of_length_lt {n : Fin 33} {evm : Evm fork Meter}
    (room : evm.stack.val.length < STACK_LIMIT) :
    pushN n evm = (GasMeter.charge evm.gas (if n.val = 0 then OPCODE_PUSH0 else OPCODE_PUSH)).map
      fun gas =>
        { evm with
          stack := ⟨pushData evm.code evm.pc n :: evm.stack.val, room⟩,
          gas, pc := evm.pc + (1 + n) } := by
  have full : ¬evm.stack.val.length = STACK_LIMIT := Nat.ne_of_lt room
  unfold pushN
  generalize (if n.val = 0 then OPCODE_PUSH0 else OPCODE_PUSH) = price
  rcases hc : GasMeter.charge evm.gas price with _ | _ <;>
    simp [hc, chargeGas, bind, Except.bind, pure, Except.pure, Except.map, pushWord,
      Stack.push, full, advance]

/-- From Spurious Dragon, EXP costs 10 plus 50 per byte of the exponent, by EIP-160. -/
theorem expStep_cons {fork : Fork} (hfork : fork ≥ .spuriousDragon) {evm : Evm fork Meter}
    {base exponent : U256} {rest : List U256} (h : evm.stack.val = base :: exponent :: rest) :
    expStep fork evm = (GasMeter.charge evm.gas (10 + 50 * exponentBytes exponent)).map fun gas =>
      { evm with
        stack := ⟨exp base exponent :: rest,
          length_cons_le (dropped := [base, exponent]) h (by simp)⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨base :: exponent :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := base) (dropped := [base, exponent]) h (by simp)
    simp only [List.length_cons] at this
    omega
  have price : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent =
      10 + 50 * exponentBytes exponent := by
    simp [OPCODE_EXP_BASE, gasSchedule, hfork]
  rw [← price]
  simp only [expStep, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas
      (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent) with
    _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- KECCAK256 pays 30, plus 6 per hashed word, plus the growth of memory to hold the bytes. -/
theorem keccak256Step_cons {evm : Evm fork Meter} {start size : U256} {rest : List U256}
    (h : evm.stack.val = start :: size :: rest) :
    keccak256Step evm =
      (GasMeter.charge evm.gas (30 + 6 * wordCount size.toNat +
        (extendMemory evm.memory.size [(start, size)]).cost)).map fun gas =>
        let memory :=
          memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy
        { evm with
          stack := ⟨keccak (memoryReadBytes memory start.toNat size.toNat) :: rest,
            length_cons_le (dropped := [start, size]) h (by simp)⟩,
          memory, gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨start :: size :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := start) (dropped := [start, size]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [keccak256Step, popWord, chargeGasAndMemory, chargeGas, pushWord, advance, hstack,
    Stack.pop, Stack.push, OPCODE_KECCAK256_BASE, OPCODE_KECCAK256_PER_WORD]
  rcases hc : GasMeter.charge evm.gas (30 + 6 * wordCount size.toNat +
      (extendMemory evm.memory.size [(start, size)]).cost) with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- Each stack instruction, and KECCAK256, keeps the message, state, substate and code. -/
theorem stackOnlyStep_sameContext {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : SameContext evm after := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | exact dupnStep_sameContext h
    | exact swapnStep_sameContext h
    | exact exchangeStep_sameContext h
    | exact unaryOp_sameContext h
    | exact binaryOp_sameContext h
    | exact ternaryOp_sameContext h
    | skip
  case exp | keccak256 =>
    simp only [expStep, keccak256Step] at h
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    first
      | exact ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
          (chargeGas_sameContext h3)).trans (pushWord_sameContext h4)).advance
      | exact ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
          (chargeGasAndMemory_sameContext h3)).trans (pushWord_sameContext h4)).advance
  case pop =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((popWord_sameContext h1).trans (chargeGas_sameContext h2)).advance
  case push =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((chargeGas_sameContext h1).trans (pushWord_sameContext h2)).advance _
  case dup =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ((chargeGas_sameContext h1).trans (pushWord_sameContext h2)).advance
  case swap =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · split at h
      · cases h
      · cases h
        have := chargeGas_sameContext h1
        exact ⟨this.message, this.state, this.substate, this.code⟩
    · cases h

/-- Each stack instruction, and KECCAK256, keeps the size of memory a multiple of 32. -/
theorem size_stackOnlyStep_mod {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some step) {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : step evm = .ok after) :
    after.memory.size % 32 = 0 := by
  suffices keep : op ≠ .keccak256 → after.memory = evm.memory by
    by_cases hk : op = .keccak256
    · subst hk
      simp only [stackOnlyStep, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
      cases h
      simp only [advance, memory_pushWord h4]
      refine size_chargeGasAndMemory_mod ?_ h3
      rw [(popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]
      exact hmod
    · rw [keep hk]
      exact hmod
  intro hk
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | exact absurd rfl hk
    | exact memory_dupnStep h
    | exact memory_swapnStep h
    | exact memory_exchangeStep h
    | exact memory_unaryOp h
    | exact memory_binaryOp h
    | exact memory_ternaryOp h
    | skip
  case exp =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h4, memory_chargeGas h3, (popWord_eq_ok h2).2.1,
      (popWord_eq_ok h1).2.1]
  case pop =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_chargeGas h2, (popWord_eq_ok h1).2.1]
  case push =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h2, memory_chargeGas h1]
  case dup =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      simp only [advance, memory_pushWord h2, memory_chargeGas h1]
  case swap =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · split at h
      · cases h
      · cases h
        simp only [advance, memory_chargeGas h1]
    · cases h

end EthLib.Execution.Evm
