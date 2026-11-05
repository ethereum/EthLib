module

public import EthLib.Execution.Evm.Memory
public import EthLib.Execution.Evm.Step

/-!
# `Evm.StackN`

DUPN, SWAPN and EXCHANGE, which reach items of the stack that DUP16 and SWAP16 cannot reach.

Each opcode reads one immediate byte: the byte of code after it, or 0 past the end of the code.

For DUPN and SWAPN, the byte encodes one depth from 17 to 235.

For EXCHANGE, it encodes two depths `n < m` with `n + m ≤ 30`.

Each instruction pays 3 gas first, then halts if its byte encodes no depth.

The analysis of jump destinations does not change.

A JUMPDEST byte right after one of these opcodes stays a valid destination.

The byte `0x5b` of JUMPDEST encodes no depth, so the opcode before it halts.

Source: [EIP-8024](https://eips.ethereum.org/EIPS/eip-8024#specification).
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The depth that the immediate byte of DUPN or SWAPN encodes, from 17 to 235.

The bytes from 91 to 127 encode no depth. -/
def decodeSingle (x : UInt8) : Option Nat :=
  if 90 < x.toNat ∧ x.toNat < 128 then none else some ((x.toNat + 145) % 256)

/-- The immediate byte of a depth `n` from 17 to 235, for DUPN or SWAPN. -/
def encodeSingle (n : Nat) : UInt8 :=
  ((n + 111) % 256).toUInt8

/-- The two depths `n < m` with `n + m ≤ 30` that the immediate byte of EXCHANGE encodes.

The bytes from 82 to 127 encode no pair.

The byte, exclusive-or 143, splits into a high half `q` and a low half `r`. -/
def decodePair (x : UInt8) : Option (Nat × Nat) :=
  if 81 < x.toNat ∧ x.toNat < 128 then none
  else
    let k := x.toNat ^^^ 143
    if k / 16 < k % 16 then some (k / 16 + 1, k % 16 + 1)
    else some (k % 16 + 1, 29 - k / 16)

/-- The immediate byte of two depths `n < m` with `n + m ≤ 30`, for EXCHANGE. -/
def encodePair (n m : Nat) : UInt8 :=
  let k := if m ≤ 16 then 16 * (n - 1) + (m - 1) else 16 * (29 - m) + (n - 1)
  (k ^^^ 143).toUInt8

/-- The stack with the items at depths `i` and `j` exchanged, from 0 at the top.

It is none when the stack has no item at one of the depths. -/
def exchangeItems (stack : Stack) (i j : Nat) : Option Stack :=
  match stack.val[i]?, stack.val[j]? with
  | some a, some b => some ⟨(stack.val.set i b).set j a, by simpa using stack.property⟩
  | _, _ => none

/-- The immediate byte of the opcode at `pc`: the next byte of code, or 0 past its end. -/
def immediateByte (code : ByteArray) (pc : Nat) : UInt8 :=
  byteAt code (pc + 1)

/-- DUPN: push a copy of the `n`th item from the top, counted from 1. -/
def dupnStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm OPCODE_DUPN
  let some n := decodeSingle (immediateByte evm.code evm.pc) | .error .invalidParameter
  match evm.stack.val[n - 1]? with
  | none => .error .stackUnderflow
  | some x =>
    let evm ← pushWord evm x
    return advance evm 2

/-- SWAPN: exchange the top item with the item `n` below it. -/
def swapnStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm OPCODE_SWAPN
  let some n := decodeSingle (immediateByte evm.code evm.pc) | .error .invalidParameter
  let some stack := exchangeItems evm.stack 0 n | .error .stackUnderflow
  return advance { evm with stack } 2

/-- EXCHANGE: exchange the items `n` and `m` below the top. -/
def exchangeStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm OPCODE_EXCHANGE
  let some (n, m) := decodePair (immediateByte evm.code evm.pc) | .error .invalidParameter
  let some stack := exchangeItems evm.stack n m | .error .stackUnderflow
  return advance { evm with stack } 2

end EthLib.Execution.Evm
