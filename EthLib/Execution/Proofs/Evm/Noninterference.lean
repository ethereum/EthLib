module

public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Instructions.Storage

/-!
# Proofs: changing state outside an instruction's read

The two frames differ only in their transaction state.

Their stack, gas meter and substate, including the warm access sets, are the same.

BALANCE depends only on the balance at its address, and SLOAD only on the word at its slot.

EXTCODEHASH depends on its account, since the empty account gives zero.

Agreement there gives the same error, or the same frame with the other state and its read recorded.

These are local steps toward the coverage of [EIP-7928, Scope and Inclusion][bal].

The warm access sets determine the charges in [EIP-2929, Storage read changes][warm].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
[warm]: https://eips.ethereum.org/EIPS/eip-2929#storage-read-changes
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256 toAddressMasked)

variable {fork : Base.Fork} {Meter : Type} [GasMeter Meter]

/-- Changing the state keeps BALANCE's result when the balance it reads agrees.

On success, the other state receives exactly the account read. -/
theorem balanceStep_congr_state {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (stack : evm.stack.val = word :: rest) (other : State.TransactionState)
    (read : (other.getAccount (toAddressMasked word)).balance =
      (evm.state.getAccount (toAddressMasked word)).balance) :
    balanceStep { evm with state := other } =
      (balanceStep evm).map (fun after =>
        { after with state := other.recordAccountRead (toAddressMasked word) }) := by
  rw [balanceStep_cons (evm := { evm with state := other }) stack, balanceStep_cons stack]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [accessAddress, berlin, ↓reduceIte, Except.map] <;>
    split <;> simp_all

/-- Changing the state keeps SLOAD's result when the word it reads agrees.

On success, the other state receives exactly the storage read. -/
theorem sloadStep_congr_state {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (stack : evm.stack.val = word :: rest) (other : State.TransactionState)
    (read : other.getStorage evm.message.currentTarget (U256.toBeBytes word) =
      evm.state.getStorage evm.message.currentTarget (U256.toBeBytes word)) :
    sloadStep { evm with state := other } =
      (sloadStep evm).map (fun after =>
        { after with
          state := other.recordStorageRead evm.message.currentTarget (U256.toBeBytes word) }) := by
  rw [sloadStep_cons (evm := { evm with state := other }) stack, sloadStep_cons stack]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [accessStorageKey, berlin, ↓reduceIte, Except.map] <;>
    split <;> simp_all

/-- Changing the state keeps EXTCODEHASH's result when the account it reads agrees.

On success, the other state receives exactly the account read. -/
theorem extcodehashStep_congr_state {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (stack : evm.stack.val = word :: rest) (other : State.TransactionState)
    (read : other.getAccount (toAddressMasked word) =
      evm.state.getAccount (toAddressMasked word)) :
    extcodehashStep { evm with state := other } =
      (extcodehashStep evm).map (fun after =>
        { after with state := other.recordAccountRead (toAddressMasked word) }) := by
  rw [extcodehashStep_cons (evm := { evm with state := other }) stack, extcodehashStep_cons stack]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [accessAddress, berlin, ↓reduceIte, Except.map] <;>
    split <;> simp_all

end EthLib.Execution.Evm
