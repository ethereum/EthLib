module

public import EthLib.Execution.Fees.BlobGas
public import EthLib.Execution.Proofs.Fees.BlobBaseFee

/-!
# Proofs: the blob gas of a transaction

A transaction without blobs uses no blob gas, so its blobs cost nothing.

The fee of the blobs grows with the excess blob gas of the block.

At an excess of 0, each blob costs exactly its blob gas, the least it can cost.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Execution.Transactions

/-- A transaction that is not of type 3 uses no blob gas. -/
theorem calculateTotalBlobGas_eq_zero {tx : Transaction} (h : ∀ b, tx ≠ .blob b) :
    calculateTotalBlobGas tx = 0 := by
  cases tx with
  | blob b => exact absurd rfl (h b)
  | _ => rfl

/-- The fee of the blobs grows with the excess blob gas. -/
theorem calculateDataFee_mono (schedule : BlobSchedule) {excessBlobGas excessBlobGas' : Nat}
    (h : excessBlobGas ≤ excessBlobGas') (tx : Transaction) :
    calculateDataFee schedule excessBlobGas tx ≤ calculateDataFee schedule excessBlobGas' tx :=
  Nat.mul_le_mul_left _ (getBaseFeePerBlobGas_mono schedule h)

/-- At an excess of 0, the fee of the blobs is their blob gas. -/
theorem calculateDataFee_zero (schedule : BlobSchedule) (tx : Transaction) :
    calculateDataFee schedule 0 tx = calculateTotalBlobGas tx := by
  simp [calculateDataFee, getBaseFeePerBlobGas_zero, MIN_BASE_FEE_PER_BLOB_GAS]

/-- The fee of the blobs is at least their blob gas, since the base fee is at least 1. -/
theorem calculateTotalBlobGas_le_calculateDataFee (schedule : BlobSchedule)
    (excessBlobGas : Nat) (tx : Transaction) :
    calculateTotalBlobGas tx ≤ calculateDataFee schedule excessBlobGas tx := by
  have h := le_getBaseFeePerBlobGas schedule excessBlobGas
  simp only [calculateDataFee]
  exact Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le (by decide) h)

end EthLib.Execution.Fees.BlobBaseFee
