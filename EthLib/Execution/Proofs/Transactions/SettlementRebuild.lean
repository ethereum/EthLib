module

public import EthLib.Execution.Proofs.Evm.Call.Rebuild
public import EthLib.Execution.Proofs.Transactions.Settlement

/-!
# Proofs: gas payments keep the property used to rebuild a block state

Buying gas raises the sender's nonce before debiting its balance.

The sender therefore keeps a nonce even when it spends its whole balance on gas.

From Paris, settlement only credits the refund and the beneficiary's priority fee.

These steps keep the rebuild property and every existing nonce or code.

The nonce and gas updates follow [Yellow Paper §6.2][execution].

The fee split from London follows [EIP-1559, Specification][fees].

This covers the fee phases, not the message or the account deletions of a whole transaction.

[fees]: https://eips.ethereum.org/EIPS/eip-1559#specification
[execution]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex#L727
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State

variable {fork : Fork}

private theorem creditEther_rebuildState {block : BlockState} {state state' : TransactionState}
    {address : Address} {amount : Nat} (valid : RebuildState block state)
    (h : creditEther fork state address amount = .ok state') :
    RebuildState block state' ∧ KeepsNonceOrCode state state' := by
  unfold creditEther at h
  split at h
  · exact valid.createEther h
  · cases h

/-- Buying gas keeps the rebuild property and leaves the sender with a nonce. -/
theorem buyGas_rebuildState {block : BlockState} {state state' : TransactionState}
    {env : BlockEnvironment fork} {sender : Address} {tx : Transaction}
    (valid : RebuildState block state) (h : buyGas env state sender tx = .ok state') :
    RebuildState block state' ∧ KeepsNonceOrCode state state' ∧
      1 ≤ (state'.getAccount sender).nonce := by
  have raised := (buyGas_sender rfl h).2.2
  unfold buyGas at h
  obtain ⟨bumped, nonce, debit⟩ := bind_ok_iff.mp h
  obtain ⟨bumpedValid, bumpedKeeps, senderNonce⟩ := valid.incrementNonce nonce
  obtain ⟨account, computed, after⟩ := TransactionState.modifyState_eq_ok_iff.mp debit
  have set : bumped.setAccountBalance fork sender account.balance = .ok state' := by
    apply TransactionState.modifyState_eq_ok_iff.mpr
    refine ⟨account, ?_, after⟩
    split at computed
    · cases computed
      rfl
    · cases computed
  obtain ⟨afterValid, afterKeeps⟩ := bumpedValid.setAccountBalance senderNonce set
  exact ⟨afterValid, bumpedKeeps.trans afterKeeps, by rw [raised]; omega⟩

/-- From Paris, refunding the sender and paying the beneficiary keep the rebuild property. -/
theorem settleGas_rebuildState (paris : .paris ≤ fork) {block : BlockState}
    {state state' : TransactionState} {env : BlockEnvironment fork} {sender : Address}
    {tx : Transaction} {gasLeft refundCounter used : Nat}
    (valid : RebuildState block state)
    (h : settleGas env state sender tx gasLeft refundCounter = .ok (state', used)) :
    RebuildState block state' ∧ KeepsNonceOrCode state state' := by
  unfold settleGas at h
  obtain ⟨refunded, refund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, pay, h⟩ := bind_ok_iff.mp h
  cases h
  have notBefore : ¬fork < .paris := Nat.not_lt_of_ge paris
  simp only [payBeneficiary, notBefore, false_and, and_false, ↓reduceIte] at pay
  obtain ⟨refundedValid, refundedKeeps⟩ := creditEther_rebuildState valid refund
  obtain ⟨paidValid, paidKeeps⟩ := creditEther_rebuildState refundedValid pay
  exact ⟨paidValid, refundedKeeps.trans paidKeeps⟩

end EthLib.Execution.Transactions
