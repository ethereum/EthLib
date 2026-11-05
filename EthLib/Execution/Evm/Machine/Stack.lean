module

public import EthLib.Base.U256
public import EthLib.Execution.Evm.Machine.Errors

/-!
# `Evm.Machine.Stack`

The stack of the EVM: a list of words, with the top first, of at most 1024 words.

A pop from the empty stack and a push onto a full stack are exceptional halts.

The subsection Exceptional Halting of the Yellow Paper, Shanghai version, sets the limit.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256)

/-- The most words that the stack holds. -/
def STACK_LIMIT : Nat := 1024

/-- A stack of words, with the top first. -/
abbrev Stack := { items : List U256 // items.length ≤ STACK_LIMIT }

namespace Stack

/-- The empty stack. -/
def empty : Stack := ⟨[], Nat.zero_le _⟩

/-- The top word and the rest of the stack, or an underflow when the stack is empty. -/
def pop : Stack → Except EvmError (U256 × Stack)
  | ⟨[], _⟩ => .error .stackUnderflow
  | ⟨x :: rest, h⟩ => .ok (x, ⟨rest, Nat.le_of_succ_le h⟩)

/-- The stack with a word on top, or an overflow when the stack is full. -/
def push (stack : Stack) (x : U256) : Except EvmError Stack :=
  if h : stack.val.length = STACK_LIMIT then .error .stackOverflow
  else .ok ⟨x :: stack.val, Nat.lt_of_le_of_ne stack.property h⟩

end Stack

end EthLib.Execution.Evm
