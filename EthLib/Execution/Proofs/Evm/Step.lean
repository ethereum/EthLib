module

public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Proofs.Evm.Stack

/-!
# Proofs: `Evm.Step`

An instruction with one, two or three operands fails with an underflow on a stack too short.

On a stack that holds its operands, it pays its price, then puts its result in place of them.

So it equals the pure function of the instruction, applied to the top words of the stack.

Each part of an instruction keeps the message, the state and the substate of the frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)

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
  obtain ⟨⟨_, _⟩, -, h⟩ := except_bind_eq_ok h
  cases h
  exact ⟨rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- A push keeps the message, the state and the substate. -/
theorem pushWord_sameContext {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : SameContext evm after := by
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- A charge keeps the message, the state and the substate. -/
theorem chargeGas_sameContext {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : SameContext evm after := by
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- A charge for a price and memory keeps the message, the state and the substate. -/
theorem chargeGasAndMemory_sameContext {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    SameContext evm after := by
  obtain ⟨_, hc, h⟩ := except_bind_eq_ok h
  cases h
  have := chargeGas_sameContext hc
  exact ⟨this.message, this.state, this.substate⟩

/-- An instruction that reads the frame keeps the message, the state and the substate. -/
theorem readFrame_sameContext {cost : Nat} {value : Evm fork Meter → U256}
    {evm after : Evm fork Meter} (h : readFrame cost value evm = .ok after) :
    SameContext evm after := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  cases h
  exact ((chargeGas_sameContext h1).trans (pushWord_sameContext h2)).advance

/-- A one-operand instruction keeps the message, the state and the substate. -/
theorem unaryOp_sameContext {cost : Nat} {f : U256 → U256} {evm after : Evm fork Meter}
    (h : unaryOp cost f evm = .ok after) : SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  cases h
  exact (((popWord_sameContext h1).trans (chargeGas_sameContext h2)).trans
    (pushWord_sameContext h3)).advance

/-- A two-operand instruction keeps the message, the state and the substate. -/
theorem binaryOp_sameContext {cost : Nat} {f : U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : binaryOp cost f evm = .ok after) : SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  cases h
  exact ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (chargeGas_sameContext h3)).trans (pushWord_sameContext h4)).advance

/-- A three-operand instruction keeps the message, the state and the substate. -/
theorem ternaryOp_sameContext {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork Meter} (h : ternaryOp cost f evm = .ok after) :
    SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, _⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h4, h⟩ := except_bind_eq_ok h
  obtain ⟨_, h5, h⟩ := except_bind_eq_ok h
  cases h
  exact (((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popWord_sameContext h3)).trans (chargeGas_sameContext h4)).trans
    (pushWord_sameContext h5)).advance

end EthLib.Execution.Evm
