module

public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Proofs.Evm.Machine.Frame
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Machine.Stack

/-!
# Proofs: `Evm.Step`

An instruction with one, two or three operands fails with an underflow on a stack too short.

On a stack that holds its operands, it pays its price, then puts its result in place of them.

So it equals the pure function of the instruction, applied to the top words of the stack.

Each part of an instruction keeps the message, the state and the substate of the frame.

A pop takes the top word of the stack and keeps memory and the return data.

A push, a charge, a charge of state gas and an instruction of up to three operands keep memory too.

A charge for gas and memory grows memory to hold each range that is not empty.

That needs a size of memory that is a multiple of 32, and the charge keeps it so.

The charge keeps every byte of memory.

A write of a range that the charge covers keeps the size a multiple of 32.

An instruction that keeps its reads keeps that size when the rest of it keeps it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 byteAt)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A stack that drops `k` words and gains one stays within the limit, for `k ≥ 1`. -/
theorem length_cons_le {stack : Stack} {dropped rest : List U256} {x : U256}
    (h : stack.val = dropped ++ rest) (nonempty : dropped ≠ []) :
    (x :: rest).length ≤ STACK_LIMIT := by
  have := stack.property
  rw [h, List.length_append] at this
  have := List.length_pos_iff.mpr nonempty
  simp only [List.length_cons]
  omega

/-- A one-operand instruction on `x`: pay, then put `f x` in place of `x`. -/
theorem unaryOp_cons {cost : Nat} {f : U256 → U256} {evm : Evm fork Meter} {x : U256}
    {rest : List U256} (h : evm.stack.val = x :: rest) :
    unaryOp cost f evm = (GasMeter.charge evm.gas cost).map fun gas =>
      { evm with stack := ⟨f x :: rest, length_cons_le (dropped := [x]) h (by simp)⟩,
                 gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨x :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := x) (dropped := [x]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [unaryOp, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas cost with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- A two-operand instruction on `x` then `y`: pay, then put `f x y` in place of both. -/
theorem binaryOp_cons {cost : Nat} {f : U256 → U256 → U256} {evm : Evm fork Meter} {x y : U256}
    {rest : List U256} (h : evm.stack.val = x :: y :: rest) :
    binaryOp cost f evm = (GasMeter.charge evm.gas cost).map fun gas =>
      { evm with stack := ⟨f x y :: rest, length_cons_le (dropped := [x, y]) h (by simp)⟩,
                 gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨x :: y :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := x) (dropped := [x, y]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [binaryOp, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas cost with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- A three-operand instruction on `x`, `y` then `z`: pay, then put `f x y z` in their place. -/
theorem ternaryOp_cons {cost : Nat} {f : U256 → U256 → U256 → U256} {evm : Evm fork Meter}
    {x y z : U256} {rest : List U256} (h : evm.stack.val = x :: y :: z :: rest) :
    ternaryOp cost f evm = (GasMeter.charge evm.gas cost).map fun gas =>
      { evm with stack := ⟨f x y z :: rest, length_cons_le (dropped := [x, y, z]) h (by simp)⟩,
                 gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨x :: y :: z :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := x) (dropped := [x, y, z]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [ternaryOp, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas cost with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- A one-operand instruction on the empty stack fails with an underflow. -/
theorem unaryOp_of_length_lt {cost : Nat} {f : U256 → U256} {evm : Evm fork Meter}
    (h : evm.stack.val.length < 1) : unaryOp cost f evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | _, _⟩
  · simp [unaryOp, popWord, hs, Stack.pop, bind, Except.bind]
  · rw [hs] at h
    simp only [List.length_cons] at h
    omega

/-- A two-operand instruction on a stack of fewer than two words fails with an underflow. -/
theorem binaryOp_of_length_lt {cost : Nat} {f : U256 → U256 → U256} {evm : Evm fork Meter}
    (h : evm.stack.val.length < 2) : binaryOp cost f evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | ⟨_, _ | _⟩, _⟩
  · simp [binaryOp, popWord, hs, Stack.pop, bind, Except.bind]
  · simp [binaryOp, popWord, hs, Stack.pop, bind, Except.bind, pure, Except.pure]
  · rw [hs] at h
    simp only [List.length_cons] at h
    omega

/-- A three-operand instruction on a stack of fewer than three words fails with an underflow. -/
theorem ternaryOp_of_length_lt {cost : Nat} {f : U256 → U256 → U256 → U256} {evm : Evm fork Meter}
    (h : evm.stack.val.length < 3) : ternaryOp cost f evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | ⟨_, _ | ⟨_, _ | _⟩⟩, _⟩
  · simp [ternaryOp, popWord, hs, Stack.pop, bind, Except.bind]
  · simp [ternaryOp, popWord, hs, Stack.pop, bind, Except.bind, pure, Except.pure]
  · simp [ternaryOp, popWord, hs, Stack.pop, bind, Except.bind, pure, Except.pure]
  · rw [hs] at h
    simp only [List.length_cons] at h
    omega

/-- The second frame has the message, the state and the substate of the first. -/
structure SameContext {Meter : Type} (before after : Evm fork Meter) : Prop where
  message : after.message = before.message
  state : after.state = before.state
  substate : after.substate = before.substate

omit [GasMeter Meter] in
/-- A frame has its own message, state and substate. -/
theorem SameContext.refl (evm : Evm fork Meter) : SameContext evm evm := ⟨rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- Two steps that each keep the message, the state and the substate keep them together. -/
theorem SameContext.trans {a b c : Evm fork Meter} (hab : SameContext a b)
    (hbc : SameContext b c) : SameContext a c :=
  ⟨hbc.message.trans hab.message, hbc.state.trans hab.state, hbc.substate.trans hab.substate⟩

omit [GasMeter Meter] in
/-- A move of the program counter keeps the message, the state and the substate. -/
theorem SameContext.advance {a b : Evm fork Meter} (h : SameContext a b) (n : Nat := 1) :
    SameContext a (Evm.advance b n) :=
  ⟨h.message, h.state, h.substate⟩

omit [GasMeter Meter] in
/-- A pop keeps the message, the state and the substate. -/
theorem popWord_sameContext {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : SameContext evm after := by
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- A push keeps the message, the state and the substate. -/
theorem pushWord_sameContext {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : SameContext evm after := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- A charge keeps the message, the state and the substate. -/
theorem chargeGas_sameContext {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : SameContext evm after := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- A charge for a price and memory keeps the message, the state and the substate. -/
theorem chargeGasAndMemory_sameContext {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    SameContext evm after := by
  obtain ⟨_, hc, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have := chargeGas_sameContext hc
  exact ⟨this.message, this.state, this.substate⟩

/-- An instruction that reads the frame keeps the message, the state and the substate. -/
theorem readFrame_sameContext {cost : Nat} {value : Evm fork Meter → U256}
    {evm after : Evm fork Meter} (h : readFrame cost value evm = .ok after) :
    SameContext evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((chargeGas_sameContext h1).trans (pushWord_sameContext h2)).advance

/-- A one-operand instruction keeps the message, the state and the substate. -/
theorem unaryOp_sameContext {cost : Nat} {f : U256 → U256} {evm after : Evm fork Meter}
    (h : unaryOp cost f evm = .ok after) : SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((popWord_sameContext h1).trans (chargeGas_sameContext h2)).trans
    (pushWord_sameContext h3)).advance

/-- A two-operand instruction keeps the message, the state and the substate. -/
theorem binaryOp_sameContext {cost : Nat} {f : U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : binaryOp cost f evm = .ok after) : SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (chargeGas_sameContext h3)).trans (pushWord_sameContext h4)).advance

/-- A three-operand instruction keeps the message, the state and the substate. -/
theorem ternaryOp_sameContext {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork Meter} (h : ternaryOp cost f evm = .ok after) :
    SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popWord_sameContext h3)).trans (chargeGas_sameContext h4)).trans
    (pushWord_sameContext h5)).advance

omit [GasMeter Meter] in
/-- A pop takes the word on top of the stack and leaves the rest.

It keeps memory and the return data. -/
theorem popWord_eq_ok {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) :
    evm.stack.val = x :: after.stack.val ∧ after.memory = evm.memory ∧
      after.returnData = evm.returnData := by
  obtain ⟨⟨y, st⟩, hp, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨Stack.pop_eq_ok_iff.mp hp, rfl, rfl⟩

omit [GasMeter Meter] in
/-- A pop from a stack with `a` on top gives `a` and leaves the rest.

It keeps memory and the return data. -/
theorem popWord_of_stack {evm after : Evm fork Meter} {a x : U256} {rest : List U256}
    (hstack : evm.stack.val = a :: rest) (h : popWord evm = .ok (x, after)) :
    a = x ∧ after.stack.val = rest ∧ after.memory = evm.memory ∧
      after.returnData = evm.returnData := by
  obtain ⟨s, m, d⟩ := popWord_eq_ok h
  rw [hstack] at s
  obtain ⟨rfl, hr⟩ := List.cons.inj s
  exact ⟨rfl, hr.symm, m, d⟩

omit [GasMeter Meter] in
/-- A push keeps memory. -/
theorem memory_pushWord {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : after.memory = evm.memory := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- A charge keeps memory. -/
theorem memory_chargeGas {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : after.memory = evm.memory := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- An instruction that reads the frame keeps memory. -/
theorem memory_readFrame {cost : Nat} {value : Evm fork Meter → U256}
    {evm after : Evm fork Meter} (h : readFrame cost value evm = .ok after) :
    after.memory = evm.memory := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp only [advance, memory_pushWord h2, memory_chargeGas h1]

/-- A one-operand instruction keeps memory. -/
theorem memory_unaryOp {cost : Nat} {f : U256 → U256} {evm after : Evm fork Meter}
    (h : unaryOp cost f evm = .ok after) : after.memory = evm.memory := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp only [advance, memory_pushWord h3, memory_chargeGas h2, (popWord_eq_ok h1).2.1]

/-- A two-operand instruction keeps memory. -/
theorem memory_binaryOp {cost : Nat} {f : U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : binaryOp cost f evm = .ok after) : after.memory = evm.memory := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp only [advance, memory_pushWord h4, memory_chargeGas h3, (popWord_eq_ok h2).2.1,
    (popWord_eq_ok h1).2.1]

/-- A three-operand instruction keeps memory. -/
theorem memory_ternaryOp {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork Meter} (h : ternaryOp cost f evm = .ok after) :
    after.memory = evm.memory := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp only [advance, memory_pushWord h5, memory_chargeGas h4, (popWord_eq_ok h3).2.1,
    (popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]

/-- A charge of state gas keeps memory. -/
theorem memory_chargeStateGas {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) : after.memory = evm.memory := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-! ## A charge for gas and memory -/

/-- A charge for gas and memory grows memory by the growth for its ranges. -/
theorem memory_chargeGasAndMemory {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    after.memory = memoryExtend evm.memory (extendMemory evm.memory.size ranges).expandBy := by
  obtain ⟨charged, hc, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp hc
  cases h
  rfl

/-- After a charge for gas and memory, memory holds every range that is not empty.

Memory must start at a size that is a multiple of 32, as every frame keeps it. -/
theorem le_size_chargeGasAndMemory {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (hmod : evm.memory.size % 32 = 0)
    (h : chargeGasAndMemory evm cost ranges = .ok after) :
    ∀ r ∈ ranges, r.2 ≠ 0 → r.1.toNat + r.2.toNat ≤ after.memory.size := by
  intro r hr hnz
  rw [memory_chargeGasAndMemory h, size_memoryExtend]
  have := le_ceil32_add_expandBy evm.memory.size ranges r hr hnz
  rwa [ceil32_of_mod hmod] at this

/-- A charge for gas and memory keeps every byte of memory. -/
theorem byteAt_chargeGasAndMemory {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) (i : Nat) :
    byteAt after.memory i = byteAt evm.memory i := by
  rw [memory_chargeGasAndMemory h, byteAt_memoryExtend]

/-- A charge for gas and memory keeps the size of memory a multiple of 32. -/
theorem size_chargeGasAndMemory_mod {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (hmod : evm.memory.size % 32 = 0)
    (h : chargeGasAndMemory evm cost ranges = .ok after) : after.memory.size % 32 = 0 := by
  rw [memory_chargeGasAndMemory h]
  exact size_memoryExtend_mod hmod ranges

/-- A write of the range that a charge for gas and memory covers keeps the size a multiple of 32.

The value must have as many bytes as the range has. -/
theorem size_memoryWrite_chargeGasAndMemory_mod {evm after : Evm fork Meter} {cost : Nat}
    {start size : U256} {value : ByteArray} (hmod : evm.memory.size % 32 = 0)
    (h : chargeGasAndMemory evm cost [(start, size)] = .ok after)
    (hsize : value.size = size.toNat) :
    (memoryWrite after.memory start.toNat value).size % 32 = 0 := by
  rw [size_memoryWrite_of_fit fun hz =>
    hsize ▸ le_size_chargeGasAndMemory hmod h (start, size) (by simp)
      (fun e => hz (by simp only at e; rw [hsize, e]; rfl))]
  exact size_chargeGasAndMemory_mod hmod h

/-! ## The size of memory after a step -/

/-- The size of memory is a multiple of 32 after a step that gives `result`.

Either the next frame has such a size, or each frame that the resume gives has it.

The resume must give it from every frame that ends the message, whatever its memory. -/
def StepResult.MemoryAligned : StepResult fork Meter → Prop
  | .next evm => evm.memory.size % 32 = 0
  | .child _ _ resume => ∀ child after, resume child = .ok after → after.memory.size % 32 = 0

/-- The rest of an instruction that keeps its reads keeps the size of memory a multiple of 32.

The rest must keep it, and so must the frame that a halt starts from. -/
theorem memoryAligned_keepReads {evm : Evm fork Meter}
    {rest : Except EvmError (StepResult fork Meter)} {result : StepResult fork Meter}
    (hmod : evm.memory.size % 32 = 0) (hrest : ∀ r, rest = .ok r → r.MemoryAligned)
    (h : keepReads evm .next rest = .ok result) : result.MemoryAligned := by
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · exact hrest _ h
  · exact hmod

end EthLib.Execution.Evm
