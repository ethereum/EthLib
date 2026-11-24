module

public import EthLib.Execution.Proofs.Blocks.SystemCall.BeaconRoots
public import EthLib.Execution.Proofs.Blocks.SystemCall.HistoryStorage
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# Proofs: a call that gets a root or a hash, with any gas

A call from an address other than the system address reads a system contract and writes nothing.

With any gas, a run either returns the word that the contract describes or ends with an error.

The message that runs such a frame rolls its state back when the frame ends with an error.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray} {bound : Nat}
  {runChild : MessageRunner fork Nat bound} {evm stopped : Evm fork Nat}

/-! ## The beacon roots contract -/

/-- A call from another address, with any gas, that ends with no error gets its root.

It holds from Shapella up to BPO5, whose frames count gas as one number, as the proof steps do. -/
theorem BeaconRoots.get_of_runFrame (hfork : .shapella ≤ fork) (_hglam : fork < .glamsterdam)
    -- The input has fewer than `2^256` bytes.
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hsize : message.data.size < 2 ^ 256)
    (start : At BeaconRoots.CODE message 0 [] .empty gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped)
    (hok : stopped.error = none) :
    -- The storage holds a root for the input, and the frame returns it.
    --
    -- Its state reads as the state it starts from, so the storage of the contract is unchanged.
    Answer state (BeaconRoots.getRoot (storageOf state message.currentTarget) message.data)
      stopped :=
  -- The theorem with fixed gas asks for 5,100 gas, which covers every path of EIP-4788.
  SpecG.low (specG_get (gas := gas + 5100) hfork hcaller hsize (Nat.le_add_left _ _))
    (start.addGas 5100) within hrun hok

/-! ## The history storage contract -/

/-- A call from another address, with any gas, that ends with no error gets its hash.

It holds from Shapella up to BPO5, whose frames count gas as one number, as the proof steps do. -/
theorem HistoryStorage.get_of_runFrame (hfork : .shapella ≤ fork) (_hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS)
    -- The block number is at least 1 and less than `2^256`.
    (hnumber : 1 ≤ message.blockEnv.number) (hbound : message.blockEnv.number < 2 ^ 256)
    -- The input has fewer than `2^256` bytes.
    (hsize : message.data.size < 2 ^ 256)
    (start : At HistoryStorage.CODE message 0 [] .empty gas state substate returnData evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped)
    (hok : stopped.error = none) :
    -- The storage holds a hash for the input, and the frame returns it.
    --
    -- Its state reads as the state it starts from, so the storage of the contract is unchanged.
    Answer state (HistoryStorage.getHash message.blockEnv.number
      (storageOf state message.currentTarget) message.data) stopped :=
  -- The theorem with fixed gas asks for 5,000 gas, which covers every path of EIP-2935.
  SpecG.low (specG_get (gas := gas + 5000) hfork hcaller hnumber hbound hsize
    (Nat.le_add_left _ _)) (start.addGas 5000) within hrun hok

end EthLib.Execution.Blocks
