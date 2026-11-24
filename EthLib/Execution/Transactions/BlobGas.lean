module

public import EthLib.Execution.Fees.BlobBaseFee
public import EthLib.Execution.Transactions.Types

/-!
# `Transactions.BlobGas`

The blob gas of a transaction, and the fee that its blobs cost.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#gas-accounting) defines both.

Each line of its two functions is marked on the line that computes it.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Execution.Transactions

/-- The blob gas of a transaction: the blob gas of one blob for each of its blobs. -/
def calculateTotalBlobGas : Transaction → Nat
  -- From Dencun, each versioned hash of a blob uses a fixed `GAS_PER_BLOB`.
  | .blob tx => GAS_PER_BLOB * tx.blobVersionedHashes.length
  -- The EIP reads only blob transactions, and the other types carry no blob.
  --
  -- So they use none.
  | _ => 0

/-- The fee that the blobs of a transaction cost, at the excess blob gas of its block.

The sender pays it apart from the fee of the execution gas. -/
def calculateDataFee (schedule : BlobSchedule) (excessBlobGas : Nat) (tx : Transaction) : Nat :=
  -- The blob gas of the transaction times the base fee per blob gas of the block.
  --
  -- The header enters through its excess blob gas, the only field that the fee reads.
  calculateTotalBlobGas tx * getBaseFeePerBlobGas schedule excessBlobGas

end EthLib.Execution.Fees.BlobBaseFee
