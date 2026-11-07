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

From Glamsterdam, the execution gas and the reservoir split the gas past the intrinsic gas.

The execution gas is at most `2^24` minus the intrinsic gas.

The reservoir is the gas limit past `2^24`.

The execution gas that a block counts for a transaction is at least the call data floor.

It is also at least the gas used before the refund, minus the state gas.

So it is at least the gas that the sender pays, minus the state gas.

Before Glamsterdam, a block counts the gas that the sender pays.

So the gas used in the header is the sum of the gas of the transactions.

Adding ether below `2^256` creates it, and an amount of at least `2^256` overflows the balance.

Settling the gas reports the gas used that the settlement counts.

Buying the gas takes exactly the fee from the sender and adds one to its nonce.

It fails if the sender does not hold the fee.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Fees.BlobBaseFee (calculateTotalBlobGas)

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

/-! ## The gas of the run -/

/-- The execution gas and the reservoir split the gas past the intrinsic gas. -/
theorem allocateGas_add (fork : Fork) (tx : Transaction) (intrinsic : Nat) :
    (allocateGas fork tx intrinsic).execution + (allocateGas fork tx intrinsic).reservoir =
      tx.gas.toNat - intrinsic := by
  unfold allocateGas
  split <;> simp only <;> omega

/-- Before Glamsterdam, all the gas past the intrinsic gas is execution gas. -/
theorem allocateGas_of_lt {fork : Fork} (hFork : fork < .glamsterdam) (tx : Transaction)
    (intrinsic : Nat) : allocateGas fork tx intrinsic = ⟨tx.gas.toNat - intrinsic, 0⟩ := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le.mpr hFork
  simp only [allocateGas, this, ↓reduceIte]

/-- From Glamsterdam, the execution gas is at most `2^24` minus the intrinsic gas. -/
theorem allocateGas_execution_le {fork : Fork} (hFork : fork ≥ .glamsterdam) (tx : Transaction)
    (intrinsic : Nat) :
    (allocateGas fork tx intrinsic).execution ≤ Evm.GasCosts.TX_MAX_GAS_LIMIT - intrinsic := by
  simp only [allocateGas, hFork, ↓reduceIte]
  exact Nat.min_le_left _ _

/-- From Glamsterdam, the reservoir is the gas limit past `2^24`.

The intrinsic gas must be at most `2^24` and at most the gas limit, as the checks ask. -/
theorem allocateGas_reservoir {fork : Fork} (hFork : fork ≥ .glamsterdam) {tx : Transaction}
    {intrinsic : Nat} (hMax : intrinsic ≤ Evm.GasCosts.TX_MAX_GAS_LIMIT)
    (hGas : intrinsic ≤ tx.gas.toNat) :
    (allocateGas fork tx intrinsic).reservoir = tx.gas.toNat - Evm.GasCosts.TX_MAX_GAS_LIMIT := by
  simp only [allocateGas, hFork, ↓reduceIte]
  omega

/-! ## The gas of the block -/

/-- Before Glamsterdam, a block counts the gas that the transaction uses, and no state gas. -/
theorem transactionBlockGas_of_lt {fork : Fork} (hFork : fork < .glamsterdam) (sender : Address)
    (tx : Transaction) (gasLeft refundCounter : Nat) (stateGasUsed : Int) :
    transactionBlockGas fork sender tx gasLeft refundCounter stateGasUsed =
      ⟨gasUsed fork sender tx gasLeft refundCounter, 0, calculateTotalBlobGas tx⟩ := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le.mpr hFork
  simp only [transactionBlockGas, this, ↓reduceIte]

/-- From Glamsterdam, a block counts the state gas used, or 0 when it is negative. -/
theorem transactionBlockGas_state {fork : Fork} (hFork : fork ≥ .glamsterdam) (sender : Address)
    (tx : Transaction) (gasLeft refundCounter : Nat) (stateGasUsed : Int) :
    (transactionBlockGas fork sender tx gasLeft refundCounter stateGasUsed).state =
      stateGasUsed.toNat := by
  simp only [transactionBlockGas, hFork, ↓reduceIte]

/-- From Glamsterdam, the execution gas of a transaction in its block is at least its floor. -/
theorem calldataFloor_le_transactionBlockGas {fork : Fork} (hFork : fork ≥ .glamsterdam)
    (sender : Address) (tx : Transaction) (gasLeft refundCounter : Nat) (stateGasUsed : Int) :
    calldataFloor fork sender tx ≤
      (transactionBlockGas fork sender tx gasLeft refundCounter stateGasUsed).execution := by
  simp only [transactionBlockGas, hFork, ↓reduceIte]
  exact Nat.le_max_right _ _

/-- From Glamsterdam, a block counts the gas used before the refund, minus the state gas.

The refund counter does not lower it. -/
theorem sub_le_transactionBlockGas {fork : Fork} (hFork : fork ≥ .glamsterdam)
    (sender : Address) (tx : Transaction) (gasLeft refundCounter : Nat) (stateGasUsed : Int) :
    tx.gas.toNat - gasLeft - stateGasUsed.toNat ≤
      (transactionBlockGas fork sender tx gasLeft refundCounter stateGasUsed).execution := by
  simp only [transactionBlockGas, hFork, ↓reduceIte]
  exact Nat.le_max_left _ _

/-- From Glamsterdam, a block counts at least the gas that the sender pays, minus the state gas. -/
theorem gasUsed_sub_le_transactionBlockGas {fork : Fork} (hFork : fork ≥ .glamsterdam)
    (sender : Address) (tx : Transaction) (gasLeft refundCounter : Nat) (stateGasUsed : Int) :
    gasUsed fork sender tx gasLeft refundCounter - stateGasUsed.toNat ≤
      (transactionBlockGas fork sender tx gasLeft refundCounter stateGasUsed).execution := by
  have hPectra : fork ≥ .pectra := Nat.le_trans (by decide) hFork
  simp only [transactionBlockGas, gasUsed, hFork, hPectra, ↓reduceIte]
  omega

/-- With no state gas, as before Glamsterdam, the gas used in the header is the execution gas. -/
theorem BlockGas.gasUsed_of_state_eq_zero {counts : BlockGas} (h : counts.state = 0) :
    counts.gasUsed = counts.execution := by
  simp [BlockGas.gasUsed, h]

/-- The execution gas of some parts of a block together is the sum of theirs. -/
theorem BlockGas.sum_execution (parts : List BlockGas) :
    (BlockGas.sum parts).execution = (parts.map (·.execution)).sum := by
  induction parts with
  | nil => rfl
  | cons p rest ih => simp [BlockGas.sum, BlockGas.add, ← ih]

/-- The state gas of some parts of a block together is the sum of theirs. -/
theorem BlockGas.sum_state (parts : List BlockGas) :
    (BlockGas.sum parts).state = (parts.map (·.state)).sum := by
  induction parts with
  | nil => rfl
  | cons p rest ih => simp [BlockGas.sum, BlockGas.add, ← ih]

/-- With no state gas in any part, the gas used in the header is the sum of the gas of the parts. -/
theorem BlockGas.gasUsed_sum {parts : List BlockGas} (h : ∀ p ∈ parts, p.state = 0) :
    (BlockGas.sum parts).gasUsed = (parts.map (·.execution)).sum := by
  rw [BlockGas.gasUsed_of_state_eq_zero, BlockGas.sum_execution]
  rw [BlockGas.sum_state]
  induction parts with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [h.1, ih h.2]

/-! ## The changes to the state -/

/-- An amount below `2^256` is created as ether at the address. -/
theorem creditEther_of_lt {fork : Fork} {state : TransactionState} {address : Address}
    {amount : Nat} (h : amount < 2 ^ 256) :
    creditEther fork state address amount =
      state.createEther fork address (BitVec.ofNat 256 amount) := by
  simp only [creditEther, h, ↓reduceIte]

/-- An amount of at least `2^256` overflows the balance, and the state is not changed. -/
theorem creditEther_of_le {fork : Fork} {state : TransactionState} {address : Address}
    {amount : Nat} (h : 2 ^ 256 ≤ amount) :
    creditEther fork state address amount = .error (.balanceOverflow address) := by
  simp only [creditEther, Nat.not_lt.mpr h, ↓reduceIte]

/-- A successful credit adds the amount to the balance of the address, and to no other. -/
theorem creditEther_balance {fork : Fork} {state state' : TransactionState}
    {target : Address} {amount : Nat} (h : creditEther fork state target amount = .ok state')
    (address : Address) :
    amount < 2 ^ 256 ∧ (state'.getAccount address).balance.toNat =
      (state.getAccount address).balance.toNat + (if target = address then amount else 0) := by
  by_cases hlt : amount < 2 ^ 256
  · rw [creditEther_of_lt hlt] at h
    refine ⟨hlt, ?_⟩
    have := (TransactionState.getAccount_createEther h address).1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using this
  · rw [creditEther_of_le (Nat.not_lt.mp hlt)] at h
    cases h

/-- Settling the gas reports the gas used that the settlement counts. -/
theorem settleGas_gasUsed {fork : Fork} {env : Evm.BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter used : Nat}
    (h : settleGas env state sender tx gasLeft refundCounter = .ok (state', used)) :
    used = gasUsed fork sender tx gasLeft refundCounter := by
  unfold settleGas at h
  cases h₁ : creditEther fork state sender
      (settlement fork (baseFeeOf env) sender tx gasLeft refundCounter).senderRefund with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok mid =>
    cases h₂ : payBeneficiary fork mid env.coinbase
        (settlement fork (baseFeeOf env) sender tx gasLeft refundCounter).priorityFee with
    | error e => simp [h₁, h₂, bind, Except.bind] at h
    | ok final =>
      simp only [h₁, h₂, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.2]
      rfl

/-- Buying the gas adds one to the nonce of the sender and takes exactly the fee from its balance.

The sender holds the fee. -/
theorem buyGas_sender {fork : Fork} {env : Evm.BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction} {fee : Nat}
    (hfee : fee = tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
      calculateTotalBlobGas tx * blobGasPriceOf env)
    (h : buyGas env state sender tx = .ok state') :
    fee ≤ (state.getAccount sender).balance.toNat ∧
      (state'.getAccount sender).balance.toNat = (state.getAccount sender).balance.toNat - fee ∧
      (state'.getAccount sender).nonce = (state.getAccount sender).nonce + 1 := by
  subst hfee
  unfold buyGas at h
  obtain ⟨mid, hmid⟩ := TransactionState.incrementNonce_isOk fork state sender
  simp only [hmid, bind, Except.bind] at h
  obtain ⟨hself, -⟩ := TransactionState.getAccount_incrementNonce hmid
  obtain ⟨account, hf, hread, -⟩ := TransactionState.modifyState_eq_ok h
  rw [hself] at hf
  dsimp only at hf
  split at hf
  · rename_i hle
    cases hf
    refine ⟨hle, ?_, ?_⟩
    · rw [hread]
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (state.getAccount sender).balance.isLt)
    · rw [hread]
  · cases hf

/-- A sender that does not hold the fee cannot buy the gas. -/
theorem buyGas_of_lt {fork : Fork} {env : Evm.BlockEnvironment fork}
    {state : TransactionState} {sender : Address} {tx : Transaction}
    (h : (state.getAccount sender).balance.toNat <
      tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
        calculateTotalBlobGas tx * blobGasPriceOf env) :
    buyGas env state sender tx = .error (.insufficientBalance sender) := by
  unfold buyGas
  obtain ⟨mid, hmid⟩ := TransactionState.incrementNonce_isOk fork state sender
  obtain ⟨hself, -⟩ := TransactionState.getAccount_incrementNonce hmid
  have hbal : (mid.getAccount sender).balance = (state.getAccount sender).balance := by
    rw [hself]
  have hnle : ¬ (tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
      calculateTotalBlobGas tx * blobGasPriceOf env ≤ (mid.getAccount sender).balance.toNat) := by
    rw [hbal]
    exact Nat.not_le.mpr h
  simp only [hmid, bind, Except.bind, TransactionState.modifyState,
    TransactionState.getAccount_recordAccountRead, hnle, ↓reduceIte]

end EthLib.Execution.Transactions
