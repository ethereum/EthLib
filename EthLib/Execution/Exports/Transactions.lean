module

public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Transactions.Validity

/-!
# `Exports.Transactions`

C-ABI exports for transactions, callable from the Python C extension.

A fork crosses the boundary as the name of its case, and a transaction as its bytes.

Each operation decodes the transaction at the fork first, and a rejection becomes an error.

The message of an error names the rule that failed, so a test can match it.
-/

public section

namespace EthLib.Execution.Transactions.Exports

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks.Exports (forkOfName)

/-- A value printed on one line, however long its numbers are. -/
def oneLine {α : Type} [Repr α] (a : α) : String :=
  (repr a).pretty 1000000

/-- An RLP error, with the index of each structure field on the way to it. -/
def rlpMessage : RlpError → String
  | .inField index error => s!"field {index}: {rlpMessage error}"
  | error => (oneLine error).replace "EthLib.Serialization.Rlp.RlpError." ""

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : TransactionError → String
  | .decoding error => s!"decoding: {rlpMessage error}"
  | .encoding error => s!"encoding: {rlpMessage error}"
  | error => (oneLine error).replace "EthLib.Execution.Transactions.TransactionError." ""

/-- Run a fallible computation down to `IO`.

The C extension turns the error into a Python exception. -/
def runTx {α : Type} (act : Except TransactionError α) : IO α :=
  match act with
  | .ok a => pure a
  | .error e => throw (IO.userError (message e))

/-- A count of gas as a `UInt64`, or an error from `2^64` on. -/
def gasToUInt64 (gas : Nat) : IO UInt64 :=
  if gas < 2 ^ 64 then pure (UInt64.ofNat gas) else throw (IO.userError "gas is 2^64 or more")

/-- The transaction that `bytes` encodes at the named fork. -/
def decodeAt (fork bytes : ByteArray) : IO (Fork × Transaction) := do
  let fork ← forkOfName fork
  return (fork, ← runTx (decodeTransaction fork bytes))

/-- The type of a transaction: 0 for a legacy transaction. -/
@[export eth_tx_type]
def typeExport (fork bytes : ByteArray) : IO UInt64 := do
  return (← decodeAt fork bytes).2.type.toUInt64

/-- The 32-byte hash of a transaction. -/
@[export eth_tx_hash]
def hashExport (fork bytes : ByteArray) : IO ByteArray := do
  let (_, tx) ← decodeAt fork bytes
  match transactionHash tx with
  | .ok hash => return ⟨hash.toArray⟩
  | .error e => throw (IO.userError s!"encoding: {rlpMessage e}")

/-- The 20-byte address of the sender of a transaction. -/
@[export eth_tx_recover_sender]
def recoverSenderExport (fork bytes : ByteArray) : IO ByteArray := do
  let (fork, tx) ← decodeAt fork bytes
  return ⟨(← runTx (recoverSender fork tx)).toArray⟩

/-- The intrinsic gas of a transaction, without the call data floor. -/
@[export eth_tx_intrinsic_gas]
def intrinsicGasExport (fork bytes : ByteArray) : IO UInt64 := do
  let (fork, tx) ← decodeAt fork bytes
  gasToUInt64 (intrinsicGas fork tx)

/-- Check a transaction alone on the chain `chainId`.

It returns 28 bytes: the 20-byte sender, then the intrinsic gas as 8 big-endian bytes. -/
@[export eth_tx_check]
def checkExport (fork : ByteArray) (chainId : UInt64) (bytes : ByteArray) : IO ByteArray := do
  let (fork, tx) ← decodeAt fork bytes
  let (sender, gas) ← runTx (checkTransaction fork chainId tx)
  let gas ← gasToUInt64 gas
  return ⟨sender.toArray ++ (List.range 8).reverse.toArray.map
    fun i => (gas >>> UInt64.ofNat (8 * i)).toUInt8⟩

end EthLib.Execution.Transactions.Exports
