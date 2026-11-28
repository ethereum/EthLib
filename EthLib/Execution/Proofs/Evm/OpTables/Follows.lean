module

public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Evm.OpTables

/-!
# Proofs: what a step that follows the tables of the opcodes does

A step takes words from the stack, leaves words there, pays a price and keeps the code.

A call or a creation does the first three in two parts, before and after its message.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A step from `before` to `after` that takes `takes` words, leaves `leaves`, pays `price`.

It keeps the code and its jump destinations.

It may instead halt with an error, after it has taken its words. -/
structure FollowsTables (takes leaves price : Nat) (before after : Evm fork Meter) : Prop where
  /-- The stack holds the words that the step takes. -/
  enough : takes ≤ before.stack.val.length
  /-- The step keeps the code. -/
  code : after.code = before.code
  /-- The step keeps the valid jump destinations. -/
  jumps : after.validJumpDestinations = before.validJumpDestinations
  /-- The step leaves its words and pays at least its price, or it halts with an error.

  It halts from a frame of the same code that has taken its words. -/
  goesOn : (after.stack.val.length + takes = before.stack.val.length + leaves ∧
      GasMeter.gasHeld after.gas + price ≤ GasMeter.gasHeld before.gas) ∨
    ∃ mid e, e.aborts = false ∧ mid.code = before.code ∧
      mid.stack.val.length + takes ≤ before.stack.val.length ∧ after = exceptionalHalt mid e

/-- A step from `before` that hands `caller` to the runner of a message, and resumes by `resume`.

The caller has taken `takes` words, paid `price`, and kept the code and its jump destinations.

Each frame that resumes holds the `leaves` words that it pushes, and keeps the code. -/
structure FollowsTablesChild (takes leaves price : Nat) (before caller : Evm fork Meter)
    (resume : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop where
  /-- The caller has taken `takes` words from the stack. -/
  taken : caller.stack.val.length + takes = before.stack.val.length
  /-- The caller has room for the words that it pushes when it resumes. -/
  room : caller.stack.val.length + leaves ≤ STACK_LIMIT
  /-- The caller has paid the price. -/
  pays : GasMeter.gasHeld caller.gas + price ≤ GasMeter.gasHeld before.gas
  /-- The caller keeps the code. -/
  code : caller.code = before.code
  /-- The caller keeps the valid jump destinations. -/
  jumps : caller.validJumpDestinations = before.validJumpDestinations
  /-- Each frame that resumes keeps the code and its destinations, and pushes `leaves` words. -/
  resume : ∀ child after, resume child = .ok after →
    after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.stack.val.length = caller.stack.val.length + leaves

/-- A result of a step from `before` that takes `takes` words, leaves `leaves` and pays `price`. -/
def StepResult.FollowsTables (takes leaves price : Nat) (before : Evm fork Meter) :
    StepResult fork Meter → Prop
  | .next after => _root_.EthLib.Execution.Evm.FollowsTables takes leaves price before after
  | .child caller _ resume => FollowsTablesChild takes leaves price before caller resume

end EthLib.Execution.Evm
