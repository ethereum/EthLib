module

public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.StackN`

DUPN, SWAPN and EXCHANGE, which reach items of the stack that DUP16 and SWAP16 cannot reach.

Source: [EIP-8024](https://eips.ethereum.org/EIPS/eip-8024#specification).
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 byteAt)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The depth that the immediate byte of DUPN or SWAPN encodes, from 17 to 235. -/
def decodeSingle (x : UInt8) : Option Nat :=
  -- EIP-8024: no depth for `90 < x < 128`, else `n = (x + 145) mod 256`.
  --
  -- So the bytes from 91 to 127 encode no depth; `0x5b`, the byte of JUMPDEST, is one of them.
  if 90 < x.toNat ∧ x.toNat < 128 then none else some ((x.toNat + 145) % 256)

/-- The immediate byte of a depth `n` from 17 to 235, for DUPN or SWAPN. -/
def encodeSingle (n : Nat) : UInt8 :=
  -- EIP-8024: `x = (n + 111) mod 256`.
  ((n + 111) % 256).toUInt8

/-- The two depths `n < m` with `n + m ≤ 30` that the immediate byte of EXCHANGE encodes. -/
def decodePair (x : UInt8) : Option (Nat × Nat) :=
  -- EIP-8024: no pair for `81 < x < 128`.
  --
  -- So the bytes from 82 to 127 encode no pair; `0x5b`, the byte of JUMPDEST, is one of them.
  if 81 < x.toNat ∧ x.toNat < 128 then none
  else
    -- `k = x XOR 143`, with `q = floor(k / 16)` and `r = k mod 16`.
    let k := x.toNat ^^^ 143
    -- `(q + 1, r + 1)` if `q < r`.
    if k / 16 < k % 16 then some (k / 16 + 1, k % 16 + 1)
    -- `(r + 1, 29 - q)` otherwise.
    else some (k % 16 + 1, 29 - k / 16)

/-- The immediate byte of two depths `n < m` with `n + m ≤ 30`, for EXCHANGE. -/
def encodePair (n m : Nat) : UInt8 :=
  -- EIP-8024: `k = 16 q + r`, with `(q, r) = (n - 1, m - 1)` for `m ≤ 16`, else `(29 - m, n - 1)`.
  --
  -- Then `x = k XOR 143`.
  let k := if m ≤ 16 then 16 * (n - 1) + (m - 1) else 16 * (29 - m) + (n - 1)
  (k ^^^ 143).toUInt8

/-- The stack with the items at depths `i` and `j` exchanged, from 0 at the top. -/
def exchangeItems (stack : Stack) (i j : Nat) : Option Stack :=
  -- None when the stack has no item at depth `i` or at depth `j`.
  match stack.val[i]?, stack.val[j]? with
  | some a, some b => some ⟨(stack.val.set i b).set j a, by simpa using stack.property⟩
  | _, _ => none

/-- The immediate byte of the opcode at `pc`: the next byte of code, or 0 past its end. -/
def immediateByte (code : ByteArray) (pc : Nat) : UInt8 :=
  -- EIP-8024: `code[pc + 1]`, which is 0 past the end of the code, as for PUSH.
  --
  -- The analysis of jump destinations does not change.
  --
  -- So a JUMPDEST byte right after one of these opcodes stays a valid destination.
  --
  -- Its byte `0x5b` encodes no depth or pair, so the opcode before it halts at step 3.
  byteAt code (pc + 1)

/-- DUPN: push a copy of the `n`th item from the top, counted from 1. -/
def dupnStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- EIP-8024, DUPN, step 1: charge 3 gas.
  let evm ← chargeGas evm OPCODE_DUPN
  -- Steps 2 to 4: `x = code[pc + 1]`, a halt for `90 < x < 128`, else `n` decoded from `x`.
  let some n := decodeSingle (immediateByte evm.code evm.pc)
    | .error (.invalidParameter (immediateByte evm.code evm.pc))
  match evm.stack.val[n - 1]? with
  -- Step 5: a halt when `n` exceeds the height of the stack.
  | none => .error .stackUnderflow
  -- Step 6: the `n`th item from the top is pushed.
  | some x =>
    let evm ← pushWord evm x
    -- Step 7: `pc = pc + 2`.
    return advance evm 2

/-- SWAPN: exchange the top item with the item `n` below it. -/
def swapnStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- EIP-8024, SWAPN, step 1: charge 3 gas.
  let evm ← chargeGas evm OPCODE_SWAPN
  -- Steps 2 to 4: `x = code[pc + 1]`, a halt for `90 < x < 128`, else `n` decoded from `x`.
  let some n := decodeSingle (immediateByte evm.code evm.pc)
    | .error (.invalidParameter (immediateByte evm.code evm.pc))
  -- Step 5: a halt when `n + 1` exceeds the height of the stack.
  --
  -- Step 6: the top item and the item `n` below it swap.
  let some stack := exchangeItems evm.stack 0 n | .error .stackUnderflow
  -- Step 7: `pc = pc + 2`.
  return advance { evm with stack } 2

/-- EXCHANGE: exchange the items `n` and `m` below the top. -/
def exchangeStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- EIP-8024, EXCHANGE, step 1: charge 3 gas.
  let evm ← chargeGas evm OPCODE_EXCHANGE
  -- Steps 2 to 4: `x = code[pc + 1]`, a halt for `81 < x < 128`, else `(n, m)` decoded from `x`.
  let some (n, m) := decodePair (immediateByte evm.code evm.pc)
    | .error (.invalidParameter (immediateByte evm.code evm.pc))
  -- Step 5: a halt when `m + 1` exceeds the height of the stack.
  --
  -- Step 6: the items `n` and `m` below the top swap.
  let some stack := exchangeItems evm.stack n m | .error .stackUnderflow
  -- Step 7: `pc = pc + 2`.
  return advance { evm with stack } 2

end EthLib.Execution.Evm
