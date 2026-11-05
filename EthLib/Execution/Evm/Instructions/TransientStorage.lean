module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.TransientStorage`

TLOAD and TSTORE: read and write a word of the transient storage of the account whose code runs.

Transient storage lives for one transaction, and a failed call rolls it back.

Each instruction costs 100, the price of a warm access, with no cold access and no refund.

TSTORE fails in a static frame.

[EIP-1153][eip1153] adds both at Dencun.

[eip1153]: https://eips.ethereum.org/EIPS/eip-1153#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- TLOAD: replace a key with the word at that key of the transient storage. -/
def tloadStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_TLOAD
  let value := evm.state.getTransientStorage evm.message.currentTarget (U256.toBeBytes word)
  let evm ← pushWord evm value
  return advance evm

/-- TSTORE: write a word at a key of the transient storage. -/
def tstoreStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let (value, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_TSTORE
  if evm.message.isStatic then
    throw .writeInStaticContext
  else
    let state :=
      evm.state.setTransientStorage evm.message.currentTarget (U256.toBeBytes word) value
    return advance { evm with state }

/-- The instruction of an opcode of transient storage, at fork `fork`.

Other opcodes give none, and so do both opcodes before Dencun. -/
def transientStorageStep (fork : Fork) :
    Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .tload => if .dencun ≤ fork then some tloadStep else none
  | .tstore => if .dencun ≤ fork then some tstoreStep else none
  | _ => none

end EthLib.Execution.Evm
