module

public import EthLib.Base.Exports.PyValue
public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.State
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Execution.Network.Pool
public import EthLib.Execution.Rpc.Eip3155
public import EthLib.Execution.Transactions.Inclusion
public import EthLib.Execution.Transactions.Network
public import EthLib.Execution.Transactions.Process
public import EthLib.Execution.Transactions.Settlement
public import EthLib.Execution.Transactions.Validity

/-!
# `Exports.Transactions`

C-ABI exports for transactions, callable from the Python C extension.

A fork crosses the boundary as the name of its case, and a transaction as its bytes.

The checks, the settlement and the run take and return typed Python values.

A number among them crosses as an `int`, and an argument that Lean cannot read fails with code 0.

Each operation decodes the transaction at the fork first.

A rejection comes back as the code and the message of its error.

The message of an error names the rule that failed, so a test can match it.

The network form of a blob transaction keeps the codes of transaction errors.

Its own errors about the blobs take codes from 101.

The type, the hash and the sender hold up to Glamsterdam, which keeps the transaction forms.

The intrinsic gas and the checks hold up to Glamsterdam.

The settlement, the checks against the block, the run and the network form hold up to BPO5.

The settlement of Glamsterdam, by EIP-7778 and EIP-8037, has no export yet.

Hegotá is not yet specified.
-/

public section

namespace EthLib.Execution.Transactions.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument forkUpTo oneLine pyExport
  rejectArgument toResult)

open EthLib.Base
open EthLib.Serialization.Rlp

/-- An RLP error, with the index of each structure field on the way to it. -/
def rlpMessage : RlpError → String
  | .inField index error => s!"field {index}: {rlpMessage error}"
  | error => (oneLine error).replace "EthLib.Serialization.Rlp.RlpError." ""

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : TransactionError → String
  | .decoding error => s!"decoding: {rlpMessage error}"
  | .encoding error => s!"encoding: {rlpMessage error}"
  | error => (oneLine error).replace "EthLib.Execution.Transactions.TransactionError." ""

/-- A rejection reaches Python with its code, and its message names the rule that failed. -/
instance : ExportError TransactionError where
  code := TransactionError.code
  message := message

/-- A count of gas as a `UInt64`, or an error from `2^64` on. -/
def gasToUInt64 (gas : Nat) : Result UInt64 :=
  -- No error type covers this bound of the binding, so its code is 0.
  if gas < 2 ^ 64 then pure (UInt64.ofNat gas) else rejectArgument none "gas is 2^64 or more"

/-- The transaction that `bytes` encodes at the named fork, if it comes no later than `last`. -/
def decodeAt (last : Fork) (fork bytes : ByteArray) : Result (Fork × Transaction) := do
  let fork ← forkUpTo last fork
  return (fork, ← toResult none (decodeTransaction fork bytes))

/-- The type of a transaction: 0 for a legacy transaction. -/
@[export eth_tx_type]
def typeExport (fork bytes : ByteArray) : Result UInt64 := do
  return (← decodeAt .glamsterdam fork bytes).2.type.toUInt64

/-- The 32-byte hash of a transaction. -/
@[export eth_tx_hash]
def hashExport (fork bytes : ByteArray) : Result ByteArray := do
  let (_, tx) ← decodeAt .glamsterdam fork bytes
  return ⟨(← toResult none ((transactionHash tx).mapError TransactionError.encoding)).toArray⟩

/-- The 20-byte address of the sender of a transaction. -/
@[export eth_tx_recover_sender]
def recoverSenderExport (fork bytes : ByteArray) : Result ByteArray := do
  let (fork, tx) ← decodeAt .glamsterdam fork bytes
  return ⟨(← toResult none (recoverSender fork tx)).toArray⟩

/-- The intrinsic gas of a transaction, without the call data floor.

From Glamsterdam it reads the sender, so the signature must name one.

Before Glamsterdam the sender changes nothing, so any address stands in for it. -/
@[export eth_tx_intrinsic_gas]
def intrinsicGasExport (fork bytes : ByteArray) : Result UInt64 := do
  let (fork, tx) ← decodeAt .glamsterdam fork bytes
  let sender ← if fork ≥ .glamsterdam then toResult none (recoverSender fork tx) else pure default
  gasToUInt64 (intrinsicGas fork sender tx)

/-- Check a transaction alone on the chain `chainId`, for its sender and its intrinsic gas.

The intrinsic gas must be below 2^64. -/
def checkOf (args : String × UInt64 × ByteArray) : Result (Address × UInt64) := do
  let (fork, chainId, bytes) := args
  let (fork, tx) ← decodeAt .glamsterdam fork.toUTF8 bytes
  let (sender, gas) ← toResult none (checkTransaction fork chainId tx)
  return (sender, ← gasToUInt64 gas)

/-- Check a transaction alone on the chain `chainId`.

The arguments are the name of the fork, the chain ID and the transaction.

It returns the 20-byte sender and the intrinsic gas, which must be below 2^64. -/
@[export eth_tx_check]
def checkExport (args : PyValue) : Result PyValue :=
  pyExport checkOf args

/-- Settle the gas of a transaction that passes the gas, nonce and fee rules.

It reads the base fee per gas of the block, the gas left and the refund counter.

The base fee must be below 2^256, and 0 before London, which has none.

The price per gas must cover the base fee, and the gas left must be at most the gas limit.

It returns the gas used, the refund of the sender, the priority fee and the burned fee. -/
def settleOf (args : String × ByteArray × Nat × Nat × Nat) : Result (Nat × Nat × Nat × Nat) := do
  let (fork, tx, baseFee, gasLeft, refundCounter) := args
  let (fork, tx) ← decodeAt .bpo5 fork.toUTF8 tx
  -- Before Glamsterdam the sender changes nothing, so any address stands in for it.
  let sender : Address := default
  let _ ← toResult none (validateTransaction fork sender tx)
  -- No error type covers these inputs of the binding, so their code is 0.
  if fork < .london ∧ baseFee ≠ 0 then
    rejectArgument none "a fork before london has no base fee"
  if 2 ^ 256 ≤ baseFee then
    rejectArgument none "base fee is 2^256 or more"
  if tx.maxFeePerGas < baseFee then
    rejectArgument none "the price per gas is below the base fee"
  if tx.gas.toNat < gasLeft then
    rejectArgument none "the gas left is above the gas limit"
  let s := settlement fork baseFee sender tx gasLeft refundCounter
  return (s.gasUsed, s.senderRefund, s.priorityFee, s.burned)

/-- Settle the gas of a transaction that passes the gas, nonce and fee rules.

The arguments are the name of the fork and the transaction.

Then come the base fee per gas, the gas left and the refund counter.

The base fee must be below 2^256, and 0 before London, which has none.

The price per gas must cover the base fee, and the gas left must be at most the gas limit.

It returns the gas used, the refund of the sender, the priority fee and the burned fee. -/
@[export eth_tx_settle]
def settleExport (args : PyValue) : Result PyValue :=
  pyExport settleOf args

/-- A message for a rejection by the block, phrased for a Python traceback. -/
def inclusionMessage : InclusionError → String
  | .transaction e => message e
  | error => (oneLine error).replace "EthLib.Execution.Transactions.InclusionError." ""

/-- A rejection by the block reaches Python with its code, and its message names the rule. -/
instance : ExportError InclusionError where
  code := InclusionError.code
  message := inclusionMessage

/-- The arguments of the check of a transaction against its block.

They are the name of the fork, the chain ID, the transaction and the state.

Then come the gas limit, the gas used and the blob gas used before the transaction.

Last come the base fee per gas and the excess blob gas of the block. -/
abbrev InBlockArgs := String × UInt64 × ByteArray × ByteArray × Nat × Nat × Nat × Nat × Nat

/-- Check that a transaction may enter its block, against a state.

The state takes the form of the state root export.

The base fee must be 0 before London, and the excess blob gas below 2^64.

It returns the sender, the price per gas and the blob gas of the transaction. -/
def checkInBlockOf (args : InBlockArgs) : Result (Address × Nat × UInt64) := do
  let (fork, chainId, tx, state, gasLimit, gasUsed, blobGasUsed, baseFee, excess) := args
  let (fork, tx) ← decodeAt .bpo5 fork.toUTF8 tx
  let pre ← toResult none (State.Exports.ofInput state)
  -- No error type covers these inputs of the binding, so their code is 0.
  if fork < .london ∧ baseFee ≠ 0 then
    rejectArgument none "a fork before london has no base fee"
  if 2 ^ 64 ≤ excess then
    rejectArgument none "excess blob gas is 2^64 or more"
  -- The checks read no other field of the block, so the others hold 0.
  let env : Evm.BlockEnvironment fork := {
    chainId, coinbase := 0, number := 0, gasLimit,
    timestamp := 0, difficulty := 0, blockHashes := [], baseFeePerGas := fun _ => baseFee,
    prevRandao := fun _ => 0, excessBlobGas := fun _ => UInt64.ofNat excess,
    parentBeaconBlockRoot := fun _ => 0, slotNumber := fun _ => 0 }
  -- Before Glamsterdam a block counts no state gas.
  let used : BlockGas := ⟨gasUsed, 0, blobGasUsed⟩
  let inc ← toResult none
    (checkInclusion chainId env used (.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩) tx)
  return (inc.sender, inc.gasPrice, ← gasToUInt64 inc.blobGasUsed)

/-- Check that a transaction may enter its block, against a state.

The arguments are the name of the fork, the chain ID, the transaction and the state.

Then come the gas limit, the gas used, the blob gas used, the base fee and the excess blob gas.

The base fee must be 0 before London, and the excess blob gas below 2^64.

It returns the sender, the price per gas and the blob gas of the transaction. -/
@[export eth_tx_check_in_block]
def checkInBlockExport (args : PyValue) : Result PyValue :=
  pyExport checkInBlockOf args

/-- Check that a node may keep a transaction from a peer in its pool, against a state.

It returns the sender, and whether the node may send the transaction whole to its peers. -/
def admitToPoolOf (args : String × UInt64 × ByteArray × ByteArray) : Result (Address × Bool) := do
  let (fork, chainId, tx, state) := args
  let (fork, tx) ← decodeAt .bpo5 fork.toUTF8 tx
  let pre ← toResult none (State.Exports.ofInput state)
  let sender ← toResult none
    (Network.admitToPool fork chainId (.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩) tx)
  return (sender, Network.mayBroadcastWhole tx)

/-- Check that a node may keep a transaction from a peer in its pool, against a state.

The arguments are the name of the fork, the chain ID, the transaction and the state.

It returns the sender, and whether the node may send the transaction whole to its peers. -/
@[export eth_tx_admit_to_pool]
def admitToPoolExport (args : PyValue) : Result PyValue :=
  pyExport admitToPoolOf args

/-! ## The run of a transaction -/

/-- The fields of a block that a run reads: a list of exactly ten items.

They are the beneficiary, the gas limit, the number, the time and the difficulty.

Then come the base fee per gas, the randomness of the beacon chain and the excess blob gas.

Then come the hashes of the blocks before, oldest first, which BLOCKHASH reads.

Last comes the slot number, which SLOTNUM reads from Glamsterdam.

A field that the fork does not have is ignored. -/
def ofEnvironmentItem (fork : Fork) (chainId : UInt64) (item : Item) :
    Except RlpError (Evm.BlockEnvironment fork) := do
  match ← item.fields 10 with
  | [coinbase, gasLimit, number, timestamp, difficulty, baseFee, prevRandao, excessBlobGas,
      blockHashes, slotNumber] =>
    let baseFee : Nat ← Codec.ofItem baseFee
    let prevRandao : Bytes32 ← Codec.ofItem prevRandao
    let excessBlobGas : UInt64 ← Codec.ofItem excessBlobGas
    let slotNumber : UInt64 ← Codec.ofItem slotNumber
    return {
      chainId, coinbase := ← Codec.ofItem coinbase,
      number := ← Codec.ofItem number, gasLimit := ← Codec.ofItem gasLimit,
      timestamp := ← Codec.ofItem timestamp, difficulty := ← Codec.ofItem difficulty,
      blockHashes := ← Codec.ofItem blockHashes, baseFeePerGas := fun _ => baseFee,
      prevRandao := fun _ => prevRandao,
      excessBlobGas := fun _ => excessBlobGas, parentBeaconBlockRoot := fun _ => 0,
      slotNumber := fun _ => slotNumber }
  | items => .error (.wrongFieldCount 10 items.length)

/-- An account of a state: its address, nonce, balance, code, and storage slots with values. -/
abbrev StateEntry := Address × Nat × U256 × ByteArray × List (Bytes32 × U256)

/-- An account of a state, with its code and its storage. -/
def stateEntry (state : State.State) (address : Address) (account : State.Account) :
    StateEntry :=
  let code := (state.code[account.codeHash]?).getD .empty
  (address, account.nonce, account.balance, code, ((state.storage[address]?).getD ∅).toList)

/-- An account of a state as an item: its address, nonce, balance, code and storage. -/
def stateEntryItem (state : State.State) (address : Address) (account : State.Account) : Item :=
  let (address, nonce, balance, code, storage) := stateEntry state address account
  .list [Codec.toItem address, Codec.toItem nonce, Codec.toItem balance, Codec.toItem code,
    .list (storage.map fun (key, value) => Item.list [Codec.toItem key, Codec.toItem value])]

/-- A message for an error that aborts a run, phrased for a Python traceback. -/
def abortMessage (error : Evm.EvmError) : String :=
  s!"the run aborted: {(oneLine error).replace "EthLib.Execution.Evm.EvmError." ""}"

/-- An error that aborts a run reaches Python with a code and its message.

An error of the state keeps its own code.

Any other abort has code 0, since no error type of the specification gives it a code. -/
instance : ExportError Evm.EvmError where
  code
    | .state s => s.code
    | _ => 0
  message := abortMessage

/-- What a run leaves, and the accounts of the state after it.

They are the state root, the hash of the encoding of the logs, the gas used and the success. -/
abbrev RunResult := ByteArray × Hash32 × Nat × Bool × List StateEntry

/-- Run one transaction on a state, in a block with no transaction before.

The state takes the form of the state root export, and the block is a list of ten items.

A transaction that may not enter the block fails with the code of its inclusion error.

An error that aborts the run has the code of its state error, or 0.

The state after it has no beneficiary reward, since a block pays that. -/
def runOf (args : String × UInt64 × ByteArray × ByteArray × ByteArray) : Result RunResult := do
  let (fork, chainId, tx, state, env) := args
  let (fork, tx) ← decodeAt .glamsterdam fork.toUTF8 tx
  let pre ← toResult none (State.Exports.ofInput state)
  let env ← toResult none ((decode env >>= ofEnvironmentItem fork chainId).mapError
    fun e => UnreadArgument.mk s!"block environment rejected: {rlpMessage e}")
  let block : State.BlockState := ⟨pre, ∅, ∅, ∅, ∅⟩
  let inc ← toResult none
    (checkInclusion chainId env ⟨0, 0, 0⟩ (.ofBlock block) tx)
  let out ← toResult none (processTransaction env block inc tx)
  let post := out.block.applyChanges
  let root ← State.Exports.rootOf post
  let logs ← toResult none ((encode (Codec.toItem out.logs.toList)).mapError
    fun e => UnreadArgument.mk s!"logs: {rlpMessage e}")
  let accounts := post.accounts.toList.map fun (address, account) =>
    stateEntry post address account
  return (root, Cryptography.Hash.Keccak.keccak256 logs, out.gasUsed, out.error.isNone, accounts)

/-- Run one transaction on a state, in a block with no transaction before.

The arguments are the name of the fork, the chain ID, the transaction, the state and the block.

The state takes the form of the state root export, and the block is a list of ten items.

A transaction that may not enter the block fails with the code of its inclusion error.

An error that aborts the run has the code of its state error, or 0.

It returns the state root, the hash of the encoding of the logs, the gas used and the success.

Last come the accounts of the state after it, each with its code and its storage.

The state after it has no beneficiary reward, since a block pays that. -/
@[export eth_tx_run]
def runExport (args : PyValue) : Result PyValue :=
  pyExport runOf args

/-- A JSON object on one line, with its fields in the order given. -/
def objectLine (fields : List (String × Lean.Json)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => (Lean.Json.str k).compress ++ ":" ++
    v.compress) ++ "}"

/-- The trace of one transaction in the lines of EIP-3155, run as the run export runs it.

The logger records what the lines require, as their configuration says. -/
def traceEip3155Of (args : String × UInt64 × ByteArray × ByteArray × ByteArray) :
    Result (List String) := do
  let (fork, chainId, tx, state, env) := args
  let (fork, tx) ← decodeAt .glamsterdam fork.toUTF8 tx
  let pre ← toResult none (State.Exports.ofInput state)
  let env ← toResult none ((decode env >>= ofEnvironmentItem fork chainId).mapError
    fun e => UnreadArgument.mk s!"block environment rejected: {rlpMessage e}")
  let block : State.BlockState := ⟨pre, ∅, ∅, ∅, ∅⟩
  let inc ← toResult none
    (checkInclusion chainId env ⟨0, 0, 0⟩ (.ofBlock block) tx)
  let (out, tracer) ← toResult none (Rpc.traceRun Rpc.eip3155Config env block inc tx)
  let root ← State.Exports.rootOf out.block.applyChanges
  let some root := Base.exactBytes? 32 root | rejectArgument none "a state root is not 32 bytes"
  return (Rpc.eip3155Lines fork (.ofRun out tracer) root).map objectLine

/-- The trace of one transaction in the lines of EIP-3155: one per step, then the summary.

The arguments are those of the run export.

They are the name of the fork, the chain ID, the transaction, the state and the block. -/
@[export eth_tx_trace_eip3155]
def traceEip3155Export (args : PyValue) : Result PyValue :=
  pyExport traceEip3155Of args

/-! ## The network form of blob transactions -/

/-- A message for a rejection of the network form, phrased for a Python traceback. -/
def networkMessage : NetworkError → String
  | .transaction e => message e
  | .wrongVersion v => s!"wrapper version {v} is not {WRAPPER_VERSION}"
  | .countMismatch h b c p =>
    s!"{h} versioned hashes, {b} blobs, {c} commitments and {p} proofs do not match"
  | .versionedHashMismatch index expected actual =>
    s!"commitment {index} hashes to {hexString expected.toList}, not to {hexString actual.toList}"
  | .kzg e => s!"kzg: {e.message}"
  | .proofRejected => "the proofs do not verify"

/-- A rejection of the network form reaches Python with its code, and its message names it. -/
instance : ExportError NetworkError where
  code := NetworkError.code
  message := networkMessage

/--
Check the network form of a blob transaction at the named fork.

It returns the bytes of the transaction alone, as a block holds it.
-/
@[export eth_tx_network_check]
def networkCheckExport (fork bytes : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .bpo5 fork
  let w ← toResult none (decodeNetwork fork bytes)
  let setup ← toResult none ((Cryptography.Kzg.Exports.embeddedSetup ()).mapError NetworkError.kzg)
  toResult none (validateNetwork setup fork w)
  toResult none ((encodeTransaction (.blob w.tx)).mapError (NetworkError.transaction ∘ .encoding))

end EthLib.Execution.Transactions.Exports
