module

public import EthLib.Execution.Fees.BlobBaseFee
public import EthLib.Execution.Transactions.Types

/-!
# `Transactions.BlobGas`

The blob gas of a transaction, and the fee that its blobs cost.

From Dencun, each blob of a transaction uses a fixed amount of blob gas.

A transaction without blobs uses none.

The sender pays the blob gas times the base fee per blob gas of the block.

That fee is apart from the fee of the execution gas.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#gas-accounting) defines both.

Each line of its two functions is marked on the line that computes it.
-/

@[expose] public section

namespace EthLib.Execution.Fees.BlobBaseFee

open EthLib.Execution.Transactions

/-- The blob gas of a transaction: the blob gas of one blob for each of its blobs. -/
def calculateTotalBlobGas : Transaction → Nat
  -- `return GAS_PER_BLOB * len(tx.blob_versioned_hashes)`, in `get_total_blob_gas`.
  | .blob tx => GAS_PER_BLOB * tx.blobVersionedHashes.length
  -- The EIP reads only blob transactions, and the other types carry no blob.
  | _ => 0

/-- The fee that the blobs of a transaction cost, at the excess blob gas of its block. -/
def calculateDataFee (schedule : BlobSchedule) (excessBlobGas : Nat) (tx : Transaction) : Nat :=
  -- `return get_total_blob_gas(tx) * get_base_fee_per_blob_gas(header)`, in `calc_blob_fee`.
  --
  -- The header enters through its excess blob gas, the only field that the fee reads.
  calculateTotalBlobGas tx * getBaseFeePerBlobGas schedule excessBlobGas

end EthLib.Execution.Fees.BlobBaseFee
