module

public import EthLib.Execution.Fees.BlobBaseFee
public import EthLib.Execution.Transactions.Types

/-!
# `Fees.BlobGas`

The blob gas of a transaction, and the fee that its blobs cost.

From Dencun, each blob of a transaction uses a fixed amount of blob gas.

A transaction without blobs uses none.

The sender pays the blob gas times the base fee per blob gas of the block.

That fee is apart from the fee of the execution gas.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#gas-accounting) defines both.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Execution.Transactions

/-- The blob gas of a transaction: the blob gas of one blob for each of its blobs. -/
def calculateTotalBlobGas : Transaction → Nat
  | .blob tx => GAS_PER_BLOB * tx.blobVersionedHashes.length
  | _ => 0

/-- The fee that the blobs of a transaction cost, at the excess blob gas of its block. -/
def calculateDataFee (schedule : BlobSchedule) (excessBlobGas : Nat) (tx : Transaction) : Nat :=
  calculateTotalBlobGas tx * getBaseFeePerBlobGas schedule excessBlobGas

end EthLib.Execution.Fees.BlobBaseFee
