module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Network
public import EthLib.Execution.Proofs.Transactions.Settlement
public import EthLib.Execution.Transactions.Inclusion

/-!
# Proofs: the rules of a transaction against its block and the state

A transaction that may enter its block passes the rules that need no state.

Its gas limit fits in the gas that the block has left, and its nonce is the nonce of the sender.

Its price per gas covers the base fee of the block, and is at most its maximum fee per gas.

The sender holds what the purchase of the gas, the blobs and the value take, so it cannot overdraw.

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

/-! ## Steps of a passing check -/

private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem failIf_ok {c : Bool} {e : InclusionError} {u : Unit} (h : failIf c e = .ok u) :
    c = false := by
  cases c
  · rfl
  · cases h

/-- What a transaction that may enter its block satisfies, in terms of its block and the state.

It passes the rules that need no state, and its signature names the sender.

Its gas fits in the gas left of the block, and its blob gas in the blob gas left.

Its maximum fee per gas covers the base fee.

From Dencun, its maximum fee per blob gas covers the base fee per blob gas.

Its nonce is the nonce of the sender, and the sender holds its most cost and its value. -/
theorem checkInclusion_ok {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {gasUsed blobGasUsed : Nat} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env gasUsed blobGasUsed state tx = .ok inc) :
    recoverSender fork tx = .ok inc.sender ∧
      validateTransaction fork inc.sender tx = .ok inc.intrinsicGas ∧
      tx.gas.toNat ≤ env.gasLimit - gasUsed ∧
      inc.blobGasUsed = calculateTotalBlobGas tx ∧
      inc.blobGasUsed ≤ maxBlobGasPerBlock fork - blobGasUsed ∧
      baseFeeOf env ≤ tx.maxFeePerGas ∧
      (0 < inc.blobGasUsed → blobGasPriceOf env ≤ tx.maxFeePerBlobGas) ∧
      inc.gasPrice = effectiveGasPrice (baseFeeOf env) tx ∧
      tx.nonce.toNat = (state.getAccount inc.sender).nonce ∧
      tx.maxGasFee + tx.value.toNat ≤ (state.getAccount inc.sender).balance.toNat := by
  unfold checkInclusion at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨g, hv, h⟩ := bind_ok h
  obtain ⟨_, hGas, h⟩ := bind_ok h
  obtain ⟨_, hBlob, h⟩ := bind_ok h
  obtain ⟨_, hFee, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, hBlobFee, h⟩ := bind_ok h
  obtain ⟨_, hLow, h⟩ := bind_ok h
  obtain ⟨_, hHigh, h⟩ := bind_ok h
  obtain ⟨_, hBal, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  have hGas := failIf_ok hGas
  have hBlob := failIf_ok hBlob
  have hFee := failIf_ok hFee
  have hBlobFee := failIf_ok hBlobFee
  have hLow := failIf_ok hLow
  have hHigh := failIf_ok hHigh
  have hBal := failIf_ok hBal
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hGas hBlob hFee hBlobFee hLow hHigh hBal
  refine ⟨mapError_ok_iff.mp hs, mapError_ok_iff.mp hv, hGas, rfl, hBlob, hFee, ?_, rfl,
    by dsimp only; omega, hBal⟩
  intro hPos
  simpa [hPos] using hBlobFee

/-! ## What a passing transaction pays -/

/-- A transaction that may enter its block pays at least the base fee per gas. -/
theorem checkInclusion_baseFee_le {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {gasUsed blobGasUsed : Nat} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env gasUsed blobGasUsed state tx = .ok inc) :
    baseFeeOf env ≤ inc.gasPrice := by
  obtain ⟨-, -, -, -, -, hFee, -, hPrice, -⟩ := checkInclusion_ok h
  exact hPrice ▸ le_effectiveGasPrice hFee

/-- A transaction that may enter its block pays at most its maximum fee per gas. -/
theorem checkInclusion_gasPrice_le {fork : Fork} {chainId : UInt64} {env : BlockEnvironment fork}
    {gasUsed blobGasUsed : Nat} {state : TransactionState} {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env gasUsed blobGasUsed state tx = .ok inc) :
    inc.gasPrice ≤ tx.maxFeePerGas := by
  obtain ⟨-, -, -, -, -, hFee, -, hPrice, -⟩ := checkInclusion_ok h
  exact hPrice ▸ effectiveGasPrice_le_maxFeePerGas hFee

/-- A transaction that may enter its block cannot overdraw its sender.

The sender holds the gas limit times the price per gas, the fee of the blobs and the value. -/
theorem checkInclusion_no_overdraw {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {gasUsed blobGasUsed : Nat} {state : TransactionState}
    {tx : Transaction} {inc : Included}
    (h : checkInclusion chainId env gasUsed blobGasUsed state tx = .ok inc) :
    tx.gas.toNat * inc.gasPrice + inc.blobGasUsed * blobGasPriceOf env + tx.value.toNat ≤
      (state.getAccount inc.sender).balance.toNat := by
  obtain ⟨-, -, -, hBlobGas, -, -, hBlobFee, -, -, hBal⟩ := checkInclusion_ok h
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
