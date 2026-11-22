module

public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.State.FreshSlots

/-!
# Proofs: the state gas of a storage write pays for its fresh slots

A slot is fresh when its word was zero before the transaction and is not zero now.

From Glamsterdam, a storage write charges state gas and may refill some.

The charge less the refill is the state gas of a new slot times the change in fresh slots.

Source: [EIP-8037][eip8037], the state gas of a new slot and its refill.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open GasCosts

variable {fork : Fork}

/-- From Glamsterdam, the state gas of a storage write, net of its refill, pays for its fresh slots.

The write charges the state gas of a new slot when it adds a fresh slot.

It refills that state gas when it clears a fresh slot. -/
theorem sstoreStateGas_sub_sstoreStateRefill (h : fork ≥ .glamsterdam)
    {tx tx' : State.TransactionState} {address : Address} {key : Bytes32} {new : U256}
    (hw : tx.setStorage address key new = .ok tx') :
    (sstoreStateGas fork (tx.getStorageOriginal address key) (tx.getStorage address key) new :
        Int) -
      sstoreStateRefill fork (tx.getStorageOriginal address key) (tx.getStorage address key) new =
      STORAGE_SET_STATE_GAS * ((tx'.freshSlots.card : Int) - tx.freshSlots.card) := by
  rw [State.TransactionState.card_freshSlots_setStorage hw]
  simp only [sstoreStateGas, sstoreStateRefill, h, true_and]
  split_ifs <;> simp_all
  -- The state gas of a new slot is a number, so the rest is linear.
  all_goals
    rw [storageSetStateGas_eq]
    omega

end EthLib.Execution.Evm
