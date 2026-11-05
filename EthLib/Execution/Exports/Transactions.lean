module

public import EthLib.Base.Exports
public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.State
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Execution.Transactions.Inclusion
public import EthLib.Execution.Transactions.Network
public import EthLib.Execution.Transactions.Settlement
public import EthLib.Execution.Transactions.Validity

/-!
# `Exports.Transactions`

C-ABI exports for transactions, callable from the Python C extension.

A fork crosses the boundary as the name of its case, and a transaction as its bytes.

Each operation decodes the transaction at the fork first.

A rejection comes back as the code and the message of its error.

The message of an error names the rule that failed, so a test can match it.

The network form of a blob transaction keeps the codes of transaction errors.

Its own errors about the blobs take codes from 101.

The type, the hash and the sender hold up to Glamsterdam, which keeps the transaction forms.

The intrinsic gas and the checks hold up to Glamsterdam.

The settlement of the gas, the checks against the block and the network form hold up to BPO5.

The settlement of Glamsterdam, by EIP-7778 and EIP-8037, has no export yet.

Hegotá is not yet specified.
-/

public section

namespace EthLib.Execution.Transactions.Exports

open EthLib.Exports (Result forkUpTo)

open EthLib.Base
open EthLib.Serialization.Rlp

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

/-- Run a fallible computation, with its error as a code and a message. -/
def runTx {α : Type} (act : Except TransactionError α) : Result α :=
  act.mapError fun e => (e.code, message e)

/-- A count of gas as a `UInt64`, or an error from `2^64` on. -/
def gasToUInt64 (gas : Nat) : Result UInt64 :=
  -- No error type covers this bound of the binding, so its code is 0.
  if gas < 2 ^ 64 then pure (UInt64.ofNat gas) else throw (0, "gas is 2^64 or more")

/-- The transaction that `bytes` encodes at the named fork, if it comes no later than `last`. -/
def decodeAt (last : Fork) (fork bytes : ByteArray) : Result (Fork × Transaction) := do
  let fork ← forkUpTo last fork
  return (fork, ← runTx (decodeTransaction fork bytes))

/-- The type of a transaction: 0 for a legacy transaction. -/
@[export eth_tx_type]
def typeExport (fork bytes : ByteArray) : Result UInt64 := do
  return (← decodeAt .glamsterdam fork bytes).2.type.toUInt64

/-- The 32-byte hash of a transaction. -/
@[export eth_tx_hash]
def hashExport (fork bytes : ByteArray) : Result ByteArray := do
  let (_, tx) ← decodeAt .glamsterdam fork bytes
  match transactionHash tx with
  | .ok hash => return ⟨hash.toArray⟩
  | .error e => throw ((TransactionError.encoding e).code, s!"encoding: {rlpMessage e}")

/-- The 20-byte address of the sender of a transaction. -/
@[export eth_tx_recover_sender]
def recoverSenderExport (fork bytes : ByteArray) : Result ByteArray := do
  let (fork, tx) ← decodeAt .glamsterdam fork bytes
  return ⟨(← runTx (recoverSender fork tx)).toArray⟩

/-- The intrinsic gas of a transaction, without the call data floor.

From Glamsterdam it reads the sender, so the signature must name one.

Before Glamsterdam the sender changes nothing, so any address stands in for it. -/
@[export eth_tx_intrinsic_gas]
def intrinsicGasExport (fork bytes : ByteArray) : Result UInt64 := do
  let (fork, tx) ← decodeAt .glamsterdam fork bytes
  let sender ← if fork ≥ .glamsterdam then runTx (recoverSender fork tx) else pure default
  gasToUInt64 (intrinsicGas fork sender tx)

/-- Check a transaction alone on the chain `chainId`.

It returns 28 bytes: the 20-byte sender, then the intrinsic gas as 8 big-endian bytes. -/
@[export eth_tx_check]
def checkExport (fork : ByteArray) (chainId : UInt64) (bytes : ByteArray) : Result ByteArray := do
  let (fork, tx) ← decodeAt .glamsterdam fork bytes
  let (sender, gas) ← runTx (checkTransaction fork chainId tx)
  let gas ← gasToUInt64 gas
  return ⟨sender.toArray ++ (List.range 8).reverse.toArray.map
    fun i => (gas >>> UInt64.ofNat (8 * i)).toUInt8⟩

/-- The number that big-endian bytes encode. -/
def numberOf (bytes : ByteArray) : Nat :=
  bytesToNat bytes.toList

/-- Settle the gas of a transaction that passes the gas, nonce and fee rules.

It reads the base fee per gas of the block, the gas left and the refund counter.

The base fee must be below 2^256, and 0 before London, which has none.

The price per gas must cover the base fee, and the gas left must be at most the gas limit.

It returns four numbers of 64 big-endian bytes each.

They are the gas used, the refund of the sender, the priority fee and the burned fee. -/
@[export eth_tx_settle]
def settleExport (fork tx baseFee gasLeft refundCounter : ByteArray) : Result ByteArray := do
  let (fork, tx) ← decodeAt .bpo5 fork tx
  -- Before Glamsterdam the sender changes nothing, so any address stands in for it.
  let sender : Address := default
  let _ ← runTx (validateTransaction fork sender tx)
  let baseFee := numberOf baseFee
  -- No error type covers these inputs of the binding, so their code is 0.
  if fork < .london ∧ baseFee ≠ 0 then
    throw (0, "a fork before london has no base fee")
  if 2 ^ 256 ≤ baseFee then
    throw (0, "base fee is 2^256 or more")
  if tx.maxFeePerGas < baseFee then
    throw (0, "the price per gas is below the base fee")
  if tx.gas.toNat < numberOf gasLeft then
    throw (0, "the gas left is above the gas limit")
  let s := settlement fork baseFee sender tx (numberOf gasLeft) (numberOf refundCounter)
  return ⟨([s.gasUsed, s.senderRefund, s.priorityFee, s.burned].flatMap (natToBytes 64)).toArray⟩

/-- A message for a rejection by the block, phrased for a Python traceback. -/
def inclusionMessage : InclusionError → String
  | .transaction e => message e
  | error => (oneLine error).replace "EthLib.Execution.Transactions.InclusionError." ""

/-- Check that a transaction may enter its block, against the state that `state` encodes.

The state takes the form of the state root export.

The block has a gas limit, a base fee and an excess blob gas, given as big-endian numbers.

Before the transaction, the block has used `gasUsed` gas and `blobGasUsed` blob gas.

The base fee must be 0 before London, and the excess blob gas below 2^64.

It returns 60 bytes: the sender, the price per gas as 32 bytes, and the blob gas as 8 bytes. -/
@[export eth_tx_check_in_block]
def checkInBlockExport (fork : ByteArray) (chainId : UInt64)
    (tx state gasLimit gasUsed blobGasUsed baseFee excessBlobGas : ByteArray) :
    Result ByteArray := do
  let (fork, tx) ← decodeAt .bpo5 fork tx
  let pre ← (State.Exports.ofInput state).mapError fun e => (e.code, e.message)
  let baseFee := numberOf baseFee
  let excess := numberOf excessBlobGas
  -- No error type covers these inputs of the binding, so their code is 0.
  if fork < .london ∧ baseFee ≠ 0 then
    throw (0, "a fork before london has no base fee")
  if 2 ^ 64 ≤ excess then
    throw (0, "excess blob gas is 2^64 or more")
  -- The checks read no other field of the block, so the others hold 0.
  let env : Evm.BlockEnvironment fork := {
    chainId := chainId.toNat, coinbase := 0, number := 0, gasLimit := numberOf gasLimit,
    timestamp := 0, difficulty := 0, blockHashes := [], baseFeePerGas := fun _ => baseFee,
    prevRandao := fun _ => 0, excessBlobGas := fun _ => UInt64.ofNat excess,
    parentBeaconBlockRoot := fun _ => 0, slotNumber := fun _ => 0 }
  -- Before Glamsterdam a block counts no state gas.
  let used : BlockGas := ⟨numberOf gasUsed, 0, numberOf blobGasUsed⟩
  let inc ← (checkInclusion chainId env used (.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩) tx).mapError
    fun e => (e.code, inclusionMessage e)
  let blobGas ← gasToUInt64 inc.blobGasUsed
  return ⟨inc.sender.toArray ++ (natToBytes 32 inc.gasPrice).toArray ++
    (List.range 8).reverse.toArray.map fun i => (blobGas >>> UInt64.ofNat (8 * i)).toUInt8⟩

/-! ## The network form of blob transactions -/

/-- A message for a rejection of the network form, phrased for a Python traceback. -/
def networkMessage : NetworkError → String
  | .transaction e => message e
  | .wrongVersion v => s!"wrapper version {v} is not {WRAPPER_VERSION}"
  | .countMismatch h b c p =>
    s!"{h} versioned hashes, {b} blobs, {c} commitments and {p} proofs do not match"
  | .versionedHashMismatch => "a commitment does not hash to its versioned hash"
  | .kzg e => s!"kzg: {e.message}"
  | .proofRejected => "the proofs do not verify"

/-- Run a fallible computation on the network form, with its error as a code and a message. -/
def runNetwork {α : Type} (act : Except NetworkError α) : Result α :=
  act.mapError fun e => (e.code, networkMessage e)

/--
Check the network form of a blob transaction at the named fork.

It returns the bytes of the transaction alone, as a block holds it.
-/
@[export eth_tx_network_check]
def networkCheckExport (fork bytes : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .bpo5 fork
  let w ← runNetwork (decodeNetwork fork bytes)
  let setup ← runNetwork (Cryptography.Kzg.Exports.embeddedSetup.mapError .kzg)
  runNetwork (validateNetwork setup fork w)
  runNetwork ((encodeTransaction (.blob w.tx)).mapError (.transaction ∘ .encoding))

end EthLib.Execution.Transactions.Exports
