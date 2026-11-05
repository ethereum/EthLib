module

public import EthLib.Execution.Proofs.State.Tracker
public import EthLib.Execution.Proofs.Transactions.Validity
public import EthLib.Execution.Transactions.Settlement

/-!
# Proofs: the settlement of the gas of a transaction

A transaction whose gas limit covers its least gas limit never uses more gas than that limit.

From Pectra, it uses at least the call data floor.

The refund is at most half of the gas used, and from London at most a fifth.

The price per gas of a transaction with a maximum fee never exceeds that maximum fee.

The wei of the gas limit split exactly into the refund, the priority fee and the burned fee.

Before London the base fee is 0, so nothing is burned.

From Spurious Dragon to Paris, a fee of 0 creates no beneficiary and deletes an empty one.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base

/-! ## The refund -/

/-- The refund is at most half of the gas used before it. -/
theorem gasRefund_le_half (fork : Fork) (used refundCounter : Nat) :
    gasRefund fork used refundCounter ≤ used / 2 := by
  unfold gasRefund maxRefundQuotient
  split
  · exact Nat.le_trans (Nat.min_le_left _ _) (Nat.div_le_div_left (by omega) (by omega))
  · exact Nat.min_le_left _ _

/-- From London, the refund is at most a fifth of the gas used before it. -/
theorem gasRefund_le_fifth {fork : Fork} (hFork : fork ≥ .london) (used refundCounter : Nat) :
    gasRefund fork used refundCounter ≤ used / 5 := by
  simp only [gasRefund, maxRefundQuotient, hFork, ↓reduceIte]
  exact Nat.min_le_left _ _

/-- The refund is at most the refund counter. -/
theorem gasRefund_le_counter (fork : Fork) (used refundCounter : Nat) :
    gasRefund fork used refundCounter ≤ refundCounter :=
  Nat.min_le_right _ _

/-! ## The gas used -/

/-- From Pectra, a transaction uses at least its call data floor. -/
theorem calldataFloor_le_gasUsed {fork : Fork} (hFork : fork ≥ .pectra) (sender : Address)
    (tx : Transaction) (gasLeft refundCounter : Nat) :
    calldataFloor fork sender tx ≤ gasUsed fork sender tx gasLeft refundCounter := by
  simp only [gasUsed, hFork, ↓reduceIte]
  exact Nat.le_max_right _ _

/-- A transaction whose gas limit covers its least gas limit uses at most its gas limit. -/
theorem gasUsed_le_gas {fork : Fork} {sender : Address} {tx : Transaction}
    (hGas : minimumGas fork sender tx ≤ tx.gas.toNat) (gasLeft refundCounter : Nat) :
    gasUsed fork sender tx gasLeft refundCounter ≤ tx.gas.toNat := by
  simp only [gasUsed]
  split
  · rename_i hFork
    have := calldataFloor_le_minimumGas hFork sender tx
    exact Nat.max_le.mpr ⟨by omega, by omega⟩
  · omega

/-! ## The price per gas -/

/-- A price per gas from a maximum fee is at most that maximum fee, if it covers the base fee. -/
theorem effectiveGasPrice.feeMarket_le {baseFee maxPriorityFee maxFee : Nat}
    (h : baseFee ≤ maxFee) :
    effectiveGasPrice.feeMarket baseFee maxPriorityFee maxFee ≤ maxFee := by
  unfold effectiveGasPrice.feeMarket
  have := Nat.min_le_right maxPriorityFee (maxFee - baseFee)
  omega

/-- A price per gas from a maximum fee is the base fee plus at most the priority fee. -/
theorem effectiveGasPrice.feeMarket_le_add (baseFee maxPriorityFee maxFee : Nat) :
    effectiveGasPrice.feeMarket baseFee maxPriorityFee maxFee ≤ maxPriorityFee + baseFee := by
  unfold effectiveGasPrice.feeMarket
  have := Nat.min_le_left maxPriorityFee (maxFee - baseFee)
  omega

/-- A price per gas from a maximum fee covers the base fee. -/
theorem effectiveGasPrice.le_feeMarket (baseFee maxPriorityFee maxFee : Nat) :
    baseFee ≤ effectiveGasPrice.feeMarket baseFee maxPriorityFee maxFee := by
  unfold effectiveGasPrice.feeMarket
  omega

/-- The price per gas of a transaction is at most its maximum fee, if that fee covers the base fee.

So a transaction that the block accepts never pays more per gas than it offers. -/
theorem effectiveGasPrice_le_maxFeePerGas {baseFee : Nat} {tx : Transaction}
    (h : baseFee ≤ tx.maxFeePerGas) : effectiveGasPrice baseFee tx ≤ tx.maxFeePerGas := by
  cases tx <;> simp only [effectiveGasPrice, Transaction.maxFeePerGas, Nat.le_refl] at * <;>
    exact effectiveGasPrice.feeMarket_le h

/-- The price per gas of a transaction covers the base fee, if its maximum fee does. -/
theorem le_effectiveGasPrice {baseFee : Nat} {tx : Transaction}
    (h : baseFee ≤ tx.maxFeePerGas) : baseFee ≤ effectiveGasPrice baseFee tx := by
  cases tx <;> simp only [effectiveGasPrice, Transaction.maxFeePerGas] at * <;>
    first | exact h | exact effectiveGasPrice.le_feeMarket _ _ _

/-! ## The payments -/

/-- The wei of the gas limit split into the refund, the priority fee and the burned fee.

The gas limit must cover the least gas limit, and the price per gas must cover the base fee. -/
theorem settlement_conserves {fork : Fork} {sender : Address} {tx : Transaction} {baseFee : Nat}
    (hGas : minimumGas fork sender tx ≤ tx.gas.toNat)
    (hPrice : baseFee ≤ effectiveGasPrice baseFee tx) (gasLeft refundCounter : Nat) :
    let s := settlement fork baseFee sender tx gasLeft refundCounter
    s.senderRefund + s.priorityFee + s.burned = tx.gas.toNat * effectiveGasPrice baseFee tx := by
  have hUsed := gasUsed_le_gas hGas gasLeft refundCounter
  simp only [settlement]
  generalize gasUsed fork sender tx gasLeft refundCounter = used at hUsed
  generalize effectiveGasPrice baseFee tx = price at hPrice
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hPrice,
    ← Nat.add_mul, Nat.sub_add_cancel hUsed]

/-- With a base fee of 0, as before London, nothing is burned and the beneficiary gets the price. -/
theorem settlement_zero_baseFee (fork : Fork) (sender : Address) (tx : Transaction)
    (gasLeft refundCounter : Nat) :
    let s := settlement fork 0 sender tx gasLeft refundCounter
    s.burned = 0 ∧ s.priorityFee = s.gasUsed * effectiveGasPrice 0 tx := by
  simp [settlement]

/-- Before London, a block has a base fee of 0. -/
theorem baseFeeOf_of_lt_london {fork : Fork} (hFork : fork < .london)
    (env : Evm.BlockEnvironment fork) : baseFeeOf env = 0 := by
  simp only [baseFeeOf]
  exact dite_eq_right_iff.mpr fun h => absurd h (Nat.not_le.mpr hFork)

/-! ## The beneficiary -/

open EthLib.Execution.State (TransactionState)

/-- From Spurious Dragon to Paris, a fee of 0 to an absent beneficiary leaves the state as it is.

So it creates no empty account. -/
theorem payBeneficiary_zero_absent {fork : Fork} (h₁ : fork ≥ .spuriousDragon)
    (h₂ : fork < .paris) {state : TransactionState} {coinbase : Address}
    (hNone : state.getAccountOptional coinbase = none) :
    payBeneficiary fork state coinbase 0 = .ok state := by
  have hBal : (state.getAccount coinbase).balance.toNat + 0 = 0 := by
    simp [TransactionState.getAccount, hNone, State.EMPTY_ACCOUNT]
  have hEmpty : state.accountExistsAndIsEmpty coinbase = false := by
    simp [TransactionState.accountExistsAndIsEmpty, hNone]
  simp only [payBeneficiary, h₁, h₂, hBal, and_self, ↓reduceIte, hEmpty, Bool.false_eq_true]

/-- From Spurious Dragon to Paris, a fee of 0 to an empty beneficiary deletes it.

[EIP-161](https://eips.ethereum.org/EIPS/eip-161#specification) counts such a fee as a touch. -/
theorem payBeneficiary_zero_empty {fork : Fork} (h₁ : fork ≥ .spuriousDragon)
    (h₂ : fork < .paris) {state : TransactionState} {coinbase : Address}
    (hEmpty : state.accountExistsAndIsEmpty coinbase = true) :
    payBeneficiary fork state coinbase 0 = .ok (state.destroyAccount coinbase) ∧
      (state.destroyAccount coinbase).getAccountOptional coinbase = none := by
  have hBal : (state.getAccount coinbase).balance.toNat + 0 = 0 := by
    rw [TransactionState.eq_empty_of_accountExistsAndIsEmpty hEmpty]
    rfl
  refine ⟨?_, TransactionState.getAccountOptional_setAccount_self _ _ _⟩
  simp only [payBeneficiary, h₁, h₂, hBal, and_self, ↓reduceIte, hEmpty]

end EthLib.Execution.Transactions
