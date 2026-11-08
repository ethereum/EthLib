module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.Fees
public import EthLib.Execution.Transactions.Envelope

/-!
# `Exports.Fees`

C-ABI exports of the base fee and the blob base fee, for the Python C extension.

Their arguments and results are typed Python values, and a number crosses as an `int`.

A fork crosses as its name, and the blob exports read the blob schedule of that fork.

A fork that is unknown, or that comes before Dencun and has no blobs, fails with code 0.

So does Hegotá, whose blob schedule is not yet specified.

So does a transaction that does not decode at the fork, or an argument that is not of its type.
-/

public section

namespace EthLib.Execution.Fees.Exports

open EthLib.Base (Fork)
open EthLib.Exports (Result PyValue forkUpTo pyExport)
open EthLib.Execution.Fees.BaseFee (calculateBaseFeePerGas)
open EthLib.Execution.Fees.BlobBaseFee

/-- The blob schedule of a named fork, from Dencun on. -/
def scheduleOfName (name : String) : Result (Fork × BlobSchedule) := do
  let fork ← forkUpTo .glamsterdam name.toUTF8
  if h : .dencun ≤ fork then
    pure (fork, blobSchedule fork h)
  else
    throw (0, "a fork before dencun has no blob schedule")

/-- The base fee per gas of a block, from its parent's gas limit, gas used and base fee. -/
@[export eth_fees_base_fee_per_gas]
def baseFeePerGasExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((gasLimit, gasUsed, baseFee) : Nat × Nat × Nat) =>
    pure (calculateBaseFeePerGas gasLimit gasUsed baseFee)) args

/-- `factor * e^(numerator / denominator)`, the integer approximation of EIP-4844.

A denominator of 0 gives 0, where the EIP divides by 0 and fails. -/
@[export eth_fees_fake_exponential]
def fakeExponentialExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((factor, numerator, denominator) : Nat × Nat × Nat) =>
    pure (fakeExponential factor numerator denominator)) args

/-- The base fee per blob gas at an excess, under the blob schedule of a fork. -/
def baseFeePerBlobGasOf (args : String × Nat) : Result Nat := do
  let (fork, excess) := args
  let (_, schedule) ← scheduleOfName fork
  pure (getBaseFeePerBlobGas schedule excess)

/-- The base fee per blob gas at an excess, under the blob schedule of a fork.

The arguments are the name of the fork and the excess blob gas. -/
@[export eth_fees_base_fee_per_blob_gas]
def baseFeePerBlobGasExport (args : PyValue) : Result PyValue :=
  pyExport baseFeePerBlobGasOf args

/-- The excess blob gas of a block at a fork, from its parent's excess, blob gas and base fee. -/
def excessBlobGasOf (args : String × Nat × Nat × Nat) : Result Nat := do
  let (fork, excess, used, baseFee) := args
  let (fork, schedule) ← scheduleOfName fork
  pure (calcExcessBlobGas fork schedule excess used baseFee)

/-- The excess blob gas of a block at a fork, from its parent's excess, blob gas and base fee.

The arguments are the name of the fork, then the three numbers of the parent. -/
@[export eth_fees_excess_blob_gas]
def excessBlobGasExport (args : PyValue) : Result PyValue :=
  pyExport excessBlobGasOf args

/-- The fee of the blobs of a transaction, decoded at a fork, at an excess blob gas. -/
def blobDataFeeOf (args : String × Nat × ByteArray) : Result Nat := do
  let (fork, excess, tx) := args
  let (fork, schedule) ← scheduleOfName fork
  let tx ← (Transactions.decodeTransaction fork tx).mapError
    fun e => (0, s!"transaction rejected: {reprStr e}")
  pure (calculateDataFee schedule excess tx)

/-- The fee of the blobs of a transaction, decoded at a fork, at an excess blob gas.

The arguments are the name of the fork, the excess blob gas and the transaction. -/
@[export eth_fees_blob_data_fee]
def blobDataFeeExport (args : PyValue) : Result PyValue :=
  pyExport blobDataFeeOf args

end EthLib.Execution.Fees.Exports
