module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Network
public import EthLib.Execution.Proofs.Transactions.Settlement
public import EthLib.Execution.Transactions.Inclusion

/-!
# Proofs: the rules of a transaction against its block and the state

A transaction that may enter its block passes the rules that need no state.

Its gas limit fits in the gas that the block has left, and its nonce is the nonce of the sender.

From Glamsterdam, its gas limit fits in the state gas that the block has left too.

Its price per gas covers the base fee of the block, and is at most its maximum fee per gas.

The sender holds what the purchase of the gas, the blobs and the value take, so it cannot overdraw.

A transaction may enter its block exactly when it passes every rule of the check.

Among them, the code of its sender is empty, or from Pectra a delegation indicator.

The codes of the errors tell their constructors apart.
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
  simp only [executionCapacity, hFork, ↓reduceIte]
  exact Nat.min_le_left _ _

/-! ## Steps of a passing check -/

private theorem failIf_ok {c : Bool} {e : InclusionError} {u : Unit} (h : failIf c e = .ok u) :
    c = false := by
  cases c
  · rfl
  · cases h

/-- What a transaction that may enter its block satisfies, in terms of its block and the state.

It passes the rules that need no state, and its signature names the sender.

Its gas, capped at 2^24 from Glamsterdam, fits in the gas left of the block.

Its blob gas fits in the blob gas left.

From Glamsterdam, the gas left of the block is execution gas.

From Glamsterdam, the gas limit also fits in the state gas left.

Its maximum fee per gas covers the base fee.

From Dencun, its maximum fee per blob gas covers the base fee per blob gas.

Its nonce is the nonce of the sender, and the sender holds its most cost and its value. -/
theorem checkInclusion_ok {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {used : BlockGas} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env used state tx = .ok inc) :
    recoverSender fork tx = .ok inc.sender ∧
      validateTransaction fork inc.sender tx = .ok inc.intrinsicGas ∧
      executionCapacity fork tx ≤ env.gasLimit - used.execution ∧
      inc.blobGasUsed = calculateTotalBlobGas tx ∧
      inc.blobGasUsed ≤ maxBlobGasPerBlock env - used.blob ∧
      baseFeeOf env ≤ tx.maxFeePerGas ∧
      (0 < inc.blobGasUsed → blobGasPriceOf env ≤ tx.maxFeePerBlobGas) ∧
      inc.gasPrice = effectiveGasPrice (baseFeeOf env) tx ∧
      tx.nonce.toNat = (state.getAccount inc.sender).nonce ∧
      tx.maxGasFee + tx.value.toNat ≤ (state.getAccount inc.sender).balance.toNat ∧
      (fork ≥ .glamsterdam → tx.gas.toNat ≤ env.gasLimit - used.state) := by
  unfold checkInclusion at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_ok_iff.mp h
  obtain ⟨g, hv, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hGas, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hState, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hBlob, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hFee, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hBlobFee, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hLow, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hHigh, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hBal, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  cases h
  have hGas := failIf_ok hGas
  have hState := failIf_ok hState
  have hBlob := failIf_ok hBlob
  have hFee := failIf_ok hFee
  have hBlobFee := failIf_ok hBlobFee
  have hLow := failIf_ok hLow
  have hHigh := failIf_ok hHigh
  have hBal := failIf_ok hBal
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hGas hBlob hFee hBlobFee hLow hHigh hBal
  refine ⟨mapError_ok_iff.mp hs, mapError_ok_iff.mp hv, hGas, rfl, hBlob, hFee, ?_, rfl,
    by dsimp only; omega, hBal, ?_⟩
  · intro hPos
    simpa [hPos] using hBlobFee
  · intro hFork
    simpa [hFork] using hState

/-- A transaction may enter its block exactly when it passes every rule of the check.

It signs no chain or the chain of the network, and its signature names the sender.

It passes the gas, nonce and fee rules, and its blobs and authorizations pass the rules.

Its gas, capped at 2^24 from Glamsterdam, fits in the gas left of the block.

Its blob gas fits in the blob gas left.

From Glamsterdam, the gas left of the block is execution gas.

From Glamsterdam, its gas limit also fits in the state gas left.

Its maximum fees cover the base fees, its nonce is the sender's, and the sender holds its cost.

The code of the sender exists, and it is empty or, from Pectra, a delegation indicator.

The result then holds the sender, the intrinsic gas, the price per gas and the blob gas. -/
theorem checkInclusion_eq_ok_iff {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {used : BlockGas} {state : TransactionState}
    {tx : Transaction} {inc : Included} :
    checkInclusion chainId env used state tx = .ok inc ↔
      checkChainId fork chainId tx = .ok () ∧
      recoverSender fork tx = .ok inc.sender ∧
      validateTransaction fork inc.sender tx = .ok inc.intrinsicGas ∧
      executionCapacity fork tx ≤ env.gasLimit - used.execution ∧
      (fork ≥ .glamsterdam → tx.gas.toNat ≤ env.gasLimit - used.state) ∧
      inc.blobGasUsed = calculateTotalBlobGas tx ∧
      inc.blobGasUsed ≤ maxBlobGasPerBlock env - used.blob ∧
      baseFeeOf env ≤ tx.maxFeePerGas ∧
      checkContents fork tx = .ok () ∧
      (0 < inc.blobGasUsed → blobGasPriceOf env ≤ tx.maxFeePerBlobGas) ∧
      inc.gasPrice = effectiveGasPrice (baseFeeOf env) tx ∧
      tx.nonce.toNat = (state.getAccount inc.sender).nonce ∧
      tx.maxGasFee + tx.value.toNat ≤ (state.getAccount inc.sender).balance.toNat ∧
      ∃ code, state.getCode (state.getAccount inc.sender).codeHash = .ok code ∧
        ((state.getAccount inc.sender).codeHash = State.EMPTY_CODE_HASH ∨
          (fork ≥ .pectra ∧ Evm.isValidDelegation code = true)) := by
  constructor
  · intro h
    obtain ⟨hs, hv, hGas, hBlobEq, hBlob, hFee, hBlobFee, hPrice, hNonce, hBal, hState⟩ :=
      checkInclusion_ok h
    unfold checkInclusion at h
    obtain ⟨_, hChain, h⟩ := bind_ok_iff.mp h
    obtain ⟨s, hs', h⟩ := bind_ok_iff.mp h
    obtain ⟨g, -, h⟩ := bind_ok_iff.mp h
    iterate 4 obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, hContents, h⟩ := bind_ok_iff.mp h
    iterate 4 obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨code, hCode, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, hEoa, h⟩ := bind_ok_iff.mp h
    cases h
    have hEoa := failIf_ok hEoa
    refine ⟨mapError_ok_iff.mp hChain, hs, hv, hGas, hState, hBlobEq, hBlob, hFee,
      mapError_ok_iff.mp hContents, hBlobFee, hPrice, hNonce, hBal, code, ?_, ?_⟩
    · cases hc : state.getCode (state.getAccount s).codeHash with
      | error e => simp [hc, Except.mapError] at hCode
      | ok c => simp_all [Except.mapError]
    · by_cases hEmpty : (state.getAccount s).codeHash = State.EMPTY_CODE_HASH
      · exact .inl hEmpty
      · right
        simpa [hEmpty] using hEoa
  · rintro ⟨hChain, hs, hv, hGas, hState, hBlobEq, hBlob, hFee, hContents, hBlobFee, hPrice,
      hNonce, hBal, code, hCode, hEoa⟩
    obtain ⟨sender, intrinsic, gasPrice, blobGas⟩ := inc
    dsimp only at *
    subst hBlobEq hPrice
    unfold checkInclusion
    have hState' : ¬(fork ≥ .glamsterdam ∧ env.gasLimit - used.state < tx.gas.toNat) :=
      fun ⟨hf, hlt⟩ => Nat.not_lt.mpr (hState hf) hlt
    have hBlobFee' : ¬(0 < calculateTotalBlobGas tx ∧
        tx.maxFeePerBlobGas < blobGasPriceOf env) :=
      fun ⟨hp, hlt⟩ => Nat.not_lt.mpr (hBlobFee hp) hlt
    have hEoa' : ¬((state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH ∧
        (!decide (fork ≥ .pectra ∧ Evm.isValidDelegation code = true)) = true) := by
      rintro ⟨hne, hbad⟩
      rcases hEoa with hempty | ⟨hp, hd⟩
      · exact hne hempty
      · simp [hp, hd] at hbad
    simp only [hChain, hs, hv, hContents, hCode, Except.mapError, bind, Except.bind, failIf,
      pure, Except.pure, Nat.not_lt.mpr hGas, Nat.not_lt.mpr hBlob,
      Nat.not_lt.mpr hFee, hState', hBlobFee', hEoa', hNonce, Nat.lt_irrefl,
      Nat.not_lt.mpr hBal, decide_false, Bool.false_eq_true, ↓reduceIte]

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
