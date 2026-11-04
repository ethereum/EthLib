module

public import EthLib.Base.Exports
public import EthLib.Execution.Fees
public import EthLib.Execution.Exports.Evm
public import EthLib.Execution.Transactions.Envelope

/-!
# `Exports.Fees`

C-ABI exports of the base fee and the blob base fee, for the Python C extension.

Each number crosses the boundary as its big-endian bytes, so no value is truncated.

A fork crosses it as its name, and the blob exports read the blob schedule of that fork.

A fork that is unknown, or that comes before Dencun and has no blobs, fails with code 0.

So does Hegotá, whose blob schedule is not yet specified.

So does a transaction that does not decode at the fork.
-/

public section

namespace EthLib.Execution.Fees.Exports

open EthLib.Base (Fork bytesToNat)
open EthLib.Exports (Result forkUpTo)
open EthLib.Execution.Evm.Exports (bytesOfNat)
open EthLib.Execution.Fees.BaseFee (calculateBaseFeePerGas)
open EthLib.Execution.Fees.BlobBaseFee

/-- The number that big-endian bytes encode. -/
def numberOf (bytes : ByteArray) : Nat :=
  bytesToNat bytes.toList

/-- The blob schedule of a named fork, from Dencun on. -/
def scheduleOfName (name : ByteArray) : Result (Fork × BlobSchedule) := do
  let fork ← forkUpTo .glamsterdam name
  if h : .dencun ≤ fork then
    pure (fork, blobSchedule fork h)
  else
    throw (0, "a fork before dencun has no blob schedule")

/-- The base fee per gas of a block, from its parent's gas limit, gas used and base fee. -/
@[export eth_fees_base_fee_per_gas]
def baseFeePerGasExport (gasLimit gasUsed baseFee : ByteArray) : ByteArray :=
  bytesOfNat (calculateBaseFeePerGas (numberOf gasLimit) (numberOf gasUsed) (numberOf baseFee))

/-- `factor * e^(numerator / denominator)`, the integer approximation of EIP-4844.

A denominator of 0 gives 0, where the EIP divides by 0 and fails. -/
@[export eth_fees_fake_exponential]
def fakeExponentialExport (factor numerator denominator : ByteArray) : ByteArray :=
  bytesOfNat (fakeExponential (numberOf factor) (numberOf numerator) (numberOf denominator))

/-- The base fee per blob gas at an excess, under the blob schedule of a fork. -/
@[export eth_fees_base_fee_per_blob_gas]
def baseFeePerBlobGasExport (fork excess : ByteArray) : Result ByteArray := do
  let (_, schedule) ← scheduleOfName fork
  pure (bytesOfNat (getBaseFeePerBlobGas schedule (numberOf excess)))

/-- The excess blob gas of a block at a fork, from its parent's excess, blob gas and base fee. -/
@[export eth_fees_excess_blob_gas]
def excessBlobGasExport (fork excess used baseFee : ByteArray) : Result ByteArray := do
  let (fork, schedule) ← scheduleOfName fork
  pure (bytesOfNat
    (calcExcessBlobGas fork schedule (numberOf excess) (numberOf used) (numberOf baseFee)))

/-- The fee of the blobs of a transaction, decoded at a fork, at an excess blob gas. -/
@[export eth_fees_blob_data_fee]
def blobDataFeeExport (fork excess tx : ByteArray) : Result ByteArray := do
  let (fork, schedule) ← scheduleOfName fork
  let tx ← (Transactions.decodeTransaction fork tx).mapError
    fun e => (0, s!"transaction rejected: {reprStr e}")
  pure (bytesOfNat (calculateDataFee schedule (numberOf excess) tx))

end EthLib.Execution.Fees.Exports
