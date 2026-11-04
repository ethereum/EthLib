module

public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Proofs.Evm.Stack

/-!
# Proofs: `Evm.Step`

An instruction with one, two or three operands fails with an underflow on a stack too short.

On a stack that holds its operands, it pays its price, then puts its result in place of them.

So it equals the pure function of the instruction, applied to the top words of the stack.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256)

variable {Meter : Type} [GasMeter Meter]

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
theorem unaryOp_cons {cost : Nat} {f : U256 → U256} {evm : Evm Meter} {x : U256}
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
theorem binaryOp_cons {cost : Nat} {f : U256 → U256 → U256} {evm : Evm Meter} {x y : U256}
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
theorem ternaryOp_cons {cost : Nat} {f : U256 → U256 → U256 → U256} {evm : Evm Meter}
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
theorem unaryOp_of_length_lt {cost : Nat} {f : U256 → U256} {evm : Evm Meter}
    (h : evm.stack.val.length < 1) : unaryOp cost f evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | _, _⟩
  · simp [unaryOp, popWord, hs, Stack.pop, bind, Except.bind]
  · rw [hs] at h
    simp only [List.length_cons] at h
    omega

/-- A two-operand instruction on a stack of fewer than two words fails with an underflow. -/
theorem binaryOp_of_length_lt {cost : Nat} {f : U256 → U256 → U256} {evm : Evm Meter}
    (h : evm.stack.val.length < 2) : binaryOp cost f evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | ⟨_, _ | _⟩, _⟩
  · simp [binaryOp, popWord, hs, Stack.pop, bind, Except.bind]
  · simp [binaryOp, popWord, hs, Stack.pop, bind, Except.bind, pure, Except.pure]
  · rw [hs] at h
    simp only [List.length_cons] at h
    omega

/-- A three-operand instruction on a stack of fewer than three words fails with an underflow. -/
theorem ternaryOp_of_length_lt {cost : Nat} {f : U256 → U256 → U256 → U256} {evm : Evm Meter}
    (h : evm.stack.val.length < 3) : ternaryOp cost f evm = .error .stackUnderflow := by
  rcases hs : evm.stack with ⟨_ | ⟨_, _ | ⟨_, _ | _⟩⟩, _⟩
  · simp [ternaryOp, popWord, hs, Stack.pop, bind, Except.bind]
  · simp [ternaryOp, popWord, hs, Stack.pop, bind, Except.bind, pure, Except.pure]
  · simp [ternaryOp, popWord, hs, Stack.pop, bind, Except.bind, pure, Except.pure]
  · rw [hs] at h
    simp only [List.length_cons] at h
    omega

end EthLib.Execution.Evm
