module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Network
public import EthLib.Execution.Proofs.Transactions.Settlement
public import EthLib.Execution.Transactions.Inclusion

/-!
# Proofs: the rules of a transaction against its block and the state

A transaction that may enter its block passes the rules that need no state.

It also fits in the gas that its block has left.

Its sender can pay for it.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Fees.BlobBaseFee

/-- Two errors with one code come from one constructor. -/
theorem InclusionError.code_injective (e₁ e₂ : InclusionError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- A wrapped transaction error has a code of at most 16, and every other code is above 200.
  have apart : ∀ (e : TransactionError) (f : InclusionError), (∀ t, f ≠ .transaction t) →
      (InclusionError.transaction e).code ≠ f.code := by
    intro e f hf hc
    have := TransactionError.code_le e
    cases f with
    | transaction t => exact hf t rfl
    | _ => simp only [InclusionError.code] at hc; rw [hc] at this; exact absurd this (by decide)
  cases e₁ with
  | transaction a =>
    cases e₂ with
    | transaction b => rfl
    | _ => exact absurd h (apart a _ (by simp))
  | _ =>
    cases e₂ with
    | transaction b => exact absurd h.symm (apart b _ (by simp))
    | _ => first | rfl | (simp only [InclusionError.code] at h; exact absurd h (by decide))

/-! ## The gas of the block -/

/-- Before Glamsterdam, the whole gas limit must fit in the gas that the block has left. -/
theorem executionCapacity_of_lt {fork : Fork} (hFork : fork < .glamsterdam) (tx : Transaction) :
    executionCapacity fork tx = tx.gas.toNat := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le.mpr hFork
  simp only [executionCapacity, this, ↓reduceIte]

/-- From Glamsterdam, the gas that must fit in the execution gas left is at most `2^24`. -/
theorem executionCapacity_le {fork : Fork} (hFork : fork ≥ .glamsterdam) (tx : Transaction) :
    executionCapacity fork tx ≤ Evm.GasCosts.TX_MAX_GAS_LIMIT := by
  simp only [executionCapacity, hFork, Bool.false_eq_true, ↓reduceIte]
  exact Nat.min_le_left _ _

/-! ## Steps of a passing check -/

private theorem failIf_ok_iff {c : Bool} {e : InclusionError} {u : Unit} :
    failIf c e = .ok u ↔ c = false := by
  cases c <;> simp [failIf]

/-- A transaction fits in what its block has left exactly when each of its three gases fits. -/
theorem checkBlockGas_ok_iff {fork : Fork} {env : BlockEnvironment fork} {used : BlockGas}
    {tx : Transaction} {u : Unit} :
    checkBlockGas env used tx = .ok u ↔
      executionCapacity fork tx ≤ env.gasLimit - used.execution ∧
        (fork ≥ .glamsterdam → tx.gas.toNat ≤ env.gasLimit - used.state) ∧
        calculateTotalBlobGas tx ≤ maxBlobGasPerBlock env - used.blob := by
  simp only [checkBlockGas, bind_ok_iff, failIf_ok_iff, decide_eq_false_iff_not, Nat.not_lt,
    not_and, exists_const]

/-- A sender may send a transaction exactly when it passes the nonce, balance and code rules.

The nonce is the sender's.

The balance covers the most that its gas and blobs can cost, and the value.

The code of the sender exists, and it is empty or, from Pectra, a delegation indicator. -/
theorem checkSender_ok_iff {fork : Fork} {state : TransactionState} {sender : Address}
    {tx : Transaction} {u : Unit} :
    checkSender fork state sender tx = .ok u ↔
      tx.nonce.toNat = (state.getAccount sender).nonce ∧
        tx.maxGasFee + tx.value.toNat ≤ (state.getAccount sender).balance.toNat ∧
        ∃ code, state.getCode (state.getAccount sender).codeHash = .ok code ∧
          ((state.getAccount sender).codeHash = State.EMPTY_CODE_HASH ∨
            (fork ≥ .pectra ∧ Evm.isValidDelegation code = true)) := by
  simp only [checkSender, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, failIf_ok_iff,
    decide_eq_false_iff_not, Nat.not_lt, exists_const]
  constructor
  · rintro ⟨hLow, hHigh, hBal, code, hCode, hEoa⟩
    refine ⟨by omega, hBal, code, ?_, ?_⟩
    · cases hc : state.getCode (state.getAccount sender).codeHash with
      | error e => simp [hc, Except.mapError] at hCode
      | ok c => simp_all [Except.mapError]
    · by_cases hEmpty : (state.getAccount sender).codeHash = State.EMPTY_CODE_HASH
      · exact .inl hEmpty
      · right
        simpa [hEmpty] using hEoa
  · rintro ⟨hNonce, hBal, code, hCode, hEoa⟩
    refine ⟨by omega, by omega, hBal, code, by simp [hCode, Except.mapError], ?_⟩
    rcases hEoa with hempty | ⟨hp, hd⟩
    · simp [hempty]
    · simp [hp, hd]

/-- A transaction may enter its block exactly when it passes every rule of the check.

The result then holds the sender, the intrinsic gas, the price per gas and the blob gas. -/
theorem checkInclusion_eq_ok_iff {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {used : BlockGas} {state : TransactionState}
    {tx : Transaction} {inc : Included} :
    checkInclusion chainId env used state tx = .ok inc ↔
      -- It signs no chain or the chain of the network.
      checkChainId fork chainId tx = .ok () ∧
      -- Its signature names the sender.
      recoverSender fork tx = .ok inc.sender ∧
      -- It passes the gas, nonce and fee rules.
      validateTransaction fork inc.sender tx = .ok inc.intrinsicGas ∧
      -- Its gas, capped at 2^24 from Glamsterdam, fits in the gas left of the block.
      --
      -- From Glamsterdam, the gas left of the block is execution gas.
      executionCapacity fork tx ≤ env.gasLimit - used.execution ∧
      -- From Glamsterdam, its gas limit also fits in the state gas left.
      (fork ≥ .glamsterdam → tx.gas.toNat ≤ env.gasLimit - used.state) ∧
      inc.blobGasUsed = calculateTotalBlobGas tx ∧
      -- Its blob gas fits in the blob gas left.
      inc.blobGasUsed ≤ maxBlobGasPerBlock env - used.blob ∧
      -- Its maximum fee per gas covers the base fee.
      baseFeeOf env ≤ tx.maxFeePerGas ∧
      -- Its blobs and authorizations pass the rules.
      checkContents fork tx = .ok () ∧
      -- When it uses blob gas, its maximum fee per blob gas covers the price per blob gas.
      (0 < inc.blobGasUsed → blobGasPriceOf env ≤ tx.maxFeePerBlobGas) ∧
      inc.gasPrice = effectiveGasPrice (baseFeeOf env) tx ∧
      -- Its nonce is the sender's.
      tx.nonce.toNat = (state.getAccount inc.sender).nonce ∧
      -- The sender holds its cost.
      tx.maxGasFee + tx.value.toNat ≤ (state.getAccount inc.sender).balance.toNat ∧
      -- The code of the sender exists, and it is empty or, from Pectra, a delegation indicator.
      ∃ code, state.getCode (state.getAccount inc.sender).codeHash = .ok code ∧
        ((state.getAccount inc.sender).codeHash = State.EMPTY_CODE_HASH ∨
          (fork ≥ .pectra ∧ Evm.isValidDelegation code = true)) := by
  obtain ⟨sender, intrinsic, gasPrice, blobGas⟩ := inc
  dsimp only
  unfold checkInclusion
  simp only [Option.isNone_none, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hg : fork ≥ .glamsterdam
  · simp only [hg, ↓reduceIte, bind_ok_iff, mapError_ok_iff, checkBlockGas_ok_iff,
      checkSender_ok_iff, failIf_ok_iff, decide_eq_false_iff_not, Nat.not_lt, not_and,
      pure, Except.pure, Except.ok.injEq, Included.mk.injEq, exists_eq_left', exists_const]
    constructor
    · rintro ⟨⟨⟩, hc, a, hs, i, hv, ⟨hGas, hState, hBlob⟩, hFee, hBlobFee, hSender, rfl, rfl, rfl,
        rfl⟩
      -- From Glamsterdam the gas, nonce and fee rules check the contents.
      exact ⟨hc, hs, hv, hGas, hState, rfl, hBlob, hFee,
        ((validateTransaction_eq_ok_iff.mp hv).2.2.2.2.2.1 hg).2.2, hBlobFee, rfl, hSender⟩
    · rintro ⟨hc, hs, hv, hGas, hState, rfl, hBlob, hFee, -, hBlobFee, rfl, hSender⟩
      exact ⟨(), hc, sender, hs, intrinsic, hv, ⟨hGas, hState, hBlob⟩, hFee, hBlobFee, hSender,
        rfl, rfl, rfl, rfl⟩
  · rw [validateTransaction_sender_of_lt_glamsterdam (Nat.lt_of_not_le hg) default sender]
    simp only [hg, ↓reduceIte, bind_ok_iff, mapError_ok_iff, checkBlockGas_ok_iff,
      checkSender_ok_iff, failIf_ok_iff, decide_eq_false_iff_not, Nat.not_lt, not_and,
      pure, Except.pure, Except.ok.injEq, Included.mk.injEq, exists_eq_left', exists_const]
    constructor
    · rintro ⟨i, hv, ⟨hGas, hState, hBlob⟩, ⟨⟩, hc, a, hs, hFee, ⟨⟩, hk, hBlobFee, hSender, rfl,
        rfl, rfl, rfl⟩
      exact ⟨hc, hs, hv, hGas, hState, rfl, hBlob, hFee, hk, hBlobFee, rfl, hSender⟩
    · rintro ⟨hc, hs, hv, hGas, hState, rfl, hBlob, hFee, hk, hBlobFee, rfl, hSender⟩
      exact ⟨intrinsic, hv, ⟨hGas, hState, hBlob⟩, (), hc, sender, hs, hFee, (), hk, hBlobFee,
        hSender, rfl, rfl, rfl, rfl⟩

/-- What a transaction that may enter its block satisfies, in terms of its block and the state.

It passes the rules that need no state. -/
theorem checkInclusion_ok {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {used : BlockGas} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env used state tx = .ok inc) :
    -- Its signature names the sender.
    recoverSender fork tx = .ok inc.sender ∧
      validateTransaction fork inc.sender tx = .ok inc.intrinsicGas ∧
      -- Its gas, capped at 2^24 from Glamsterdam, fits in the gas left of the block.
      --
      -- From Glamsterdam, the gas left of the block is execution gas.
      executionCapacity fork tx ≤ env.gasLimit - used.execution ∧
      inc.blobGasUsed = calculateTotalBlobGas tx ∧
      -- Its blob gas fits in the blob gas left.
      inc.blobGasUsed ≤ maxBlobGasPerBlock env - used.blob ∧
      -- Its maximum fee per gas covers the base fee.
      baseFeeOf env ≤ tx.maxFeePerGas ∧
      -- When it uses blob gas, its maximum fee per blob gas covers the price per blob gas.
      (0 < inc.blobGasUsed → blobGasPriceOf env ≤ tx.maxFeePerBlobGas) ∧
      inc.gasPrice = effectiveGasPrice (baseFeeOf env) tx ∧
      -- Its nonce is the nonce of the sender.
      tx.nonce.toNat = (state.getAccount inc.sender).nonce ∧
      -- The sender holds the most that its gas and blobs can cost, and its value.
      tx.maxGasFee + tx.value.toNat ≤ (state.getAccount inc.sender).balance.toNat ∧
      -- From Glamsterdam, the gas limit also fits in the state gas left.
      (fork ≥ .glamsterdam → tx.gas.toNat ≤ env.gasLimit - used.state) := by
  obtain ⟨-, hs, hv, hGas, hState, hBlobEq, hBlob, hFee, -, hBlobFee, hPrice, hNonce, hBal, -⟩ :=
    checkInclusion_eq_ok_iff.mp h
  exact ⟨hs, hv, hGas, hBlobEq, hBlob, hFee, hBlobFee, hPrice, hNonce, hBal, hState⟩

/-- A transaction that may enter its block has a type that exists at the fork of the block. -/
theorem checkInclusion_fork_le {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {used : BlockGas} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env used state tx = .ok inc) : tx.fork ≤ fork :=
  validateTransaction_fork_le (checkInclusion_ok h).2.1

/-! ## What a passing transaction pays -/

/-- A transaction that may enter its block pays at least the base fee per gas. -/
theorem checkInclusion_baseFee_le {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {used : BlockGas} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env used state tx = .ok inc) :
    baseFeeOf env ≤ inc.gasPrice := by
  obtain ⟨-, -, -, -, -, hFee, -, hPrice, -⟩ := checkInclusion_ok h
  exact hPrice ▸ le_effectiveGasPrice hFee

/-- A transaction that may enter its block pays at most its maximum fee per gas. -/
theorem checkInclusion_gasPrice_le {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {used : BlockGas} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env used state tx = .ok inc) :
    inc.gasPrice ≤ tx.maxFeePerGas := by
  obtain ⟨-, -, -, -, -, hFee, -, hPrice, -⟩ := checkInclusion_ok h
  exact hPrice ▸ effectiveGasPrice_le_maxFeePerGas hFee

/-- A transaction that may enter its block cannot overdraw its sender.

The sender holds the gas limit times the price per gas, the fee of the blobs and the value. -/
theorem checkInclusion_no_overdraw {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {used : BlockGas} {state : TransactionState}
    {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env used state tx = .ok inc) :
    tx.gas.toNat * inc.gasPrice + inc.blobGasUsed * blobGasPriceOf env + tx.value.toNat ≤
      (state.getAccount inc.sender).balance.toNat := by
  obtain ⟨-, -, -, hBlobGas, -, -, hBlobFee, -, -, hBal, -⟩ := checkInclusion_ok h
  have hPrice := checkInclusion_gasPrice_le h
  have hGas : tx.gas.toNat * inc.gasPrice ≤ tx.gas.toNat * tx.maxFeePerGas :=
    Nat.mul_le_mul_left _ hPrice
  have hBlob : inc.blobGasUsed * blobGasPriceOf env ≤ inc.blobGasUsed * tx.maxFeePerBlobGas := by
    rcases Nat.eq_zero_or_pos inc.blobGasUsed with h0 | hPos
    · simp [h0]
    · exact Nat.mul_le_mul_left _ (hBlobFee hPos)
  unfold Transaction.maxGasFee at hBal
  rw [← hBlobGas] at hBal
  omega

end EthLib.Execution.Transactions
