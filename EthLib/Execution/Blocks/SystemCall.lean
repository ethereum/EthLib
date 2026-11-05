module

public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Transactions.Process

/-!
# `Blocks.SystemCall`

The calls that a block makes to system contracts, outside any transaction.

A system call comes from the system address, with 30,000,000 gas and no value.

Its gas does not count against the gas limit of the block, and nobody pays for it.

It runs the code of its contract as the message of a transaction does.

It starts with no address accessed, and its price per gas is the base fee of the block.

Its writes join the block.

It has no receipt, so its logs enter no receipt.

From Dencun, a block starts with a call to the beacon roots contract.

Its data is the root of the parent beacon block, and the contract stores it.

From Pectra, a second call follows, to the history storage contract.

Its data is the hash of the parent block, and the contract stores it.

These two calls are unchecked: the block goes on when the contract has no code or the call fails.

From Pectra, a block ends with calls to the withdrawal and consolidation request contracts.

Each has no data, and returns the requests of its type, in the order of its queue.

These two calls are checked: the block is invalid when the contract has no code or the call fails.

Each EIP states its call in its section on block processing or on the system call:

- [EIP-4788][eip-4788], the beacon roots contract
- [EIP-2935][eip-2935], the history storage contract
- [EIP-7002][eip-7002], the withdrawal request contract
- [EIP-7251][eip-7251], the consolidation request contract

A list of requests with no data is left out, as [EIP-7685][eip-7685] leaves it out of its hash.

From Glamsterdam the calls fail as not yet specified, as the run of a transaction does.

[eip-4788]: https://eips.ethereum.org/EIPS/eip-4788#block-processing
[eip-2935]: https://eips.ethereum.org/EIPS/eip-2935#block-processing
[eip-7002]: https://eips.ethereum.org/EIPS/eip-7002#system-call
[eip-7251]: https://eips.ethereum.org/EIPS/eip-7251#system-call
[eip-7685]: https://eips.ethereum.org/EIPS/eip-7685#block-header
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)
open EthLib.Execution.Transactions (processMessageCall)

/-! ## Addresses and gas -/

/-- The gas of a system call. -/
def SYSTEM_TRANSACTION_GAS : Nat := 30000000

/-- The beacon roots contract of EIP-4788. -/
def BEACON_ROOTS_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02)

/-- The history storage contract of EIP-2935. -/
def HISTORY_STORAGE_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0x0000F90827F1C53a10cb7A02335B175320002935)

/-- The withdrawal request contract of EIP-7002. -/
def WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0x00000961Ef480Eb55e80D19ad83579A64c007002)

/-- The consolidation request contract of EIP-7251. -/
def CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0x0000BBdDc7CE488642fb579F8B00f3a590007251)

/-! ## The call -/

/-- What a system call leaves. -/
structure SystemCallOutput where
  /-- The block state, with the writes of the call. -/
  block : BlockState
  /-- The data that the call returned. -/
  output : ByteArray
  /-- The error that stopped the call, or none when it succeeded. -/
  error : Option EvmError

/-- The message of a system call to `target` with the data `data`, at `fork`.

Its code is empty until the call reads the code of `target`. -/
def systemMessage {fork : Fork} (env : BlockEnvironment fork) (target : Address)
    (data : ByteArray) : Message fork where
  blockEnv := env
  txEnv := { origin := SYSTEM_ADDRESS
             gasPrice := if h : .london ≤ fork then env.baseFeePerGas h else 0
             blobVersionedHashes := fun _ => [] }
  caller := SYSTEM_ADDRESS
  target := some target
  currentTarget := target
  gas := SYSTEM_TRANSACTION_GAS
  value := 0
  data := data
  codeAddress := some target
  code := .empty
  depth := 0
  shouldTransferValue := false
  isStatic := false
  disablePrecompiles := false

/-- Make a system call to `target` with the data `data`, on the block state `block` at `fork`.

A call that fails leaves the block state as it was.

It fails only with an error that aborts the whole execution, such as missing code.

From Glamsterdam it fails, since the rules of that fork are not yet specified here. -/
def systemCall {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (target : Address) (data : ByteArray) : Except EvmError SystemCallOutput := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let out ← processMessageCall (Meter := Nat) env.chainId (systemMessage env target data)
    (TransactionState.ofBlock block) Substate.empty
  return ⟨out.state.incorporateTxIntoBlock.parent, out.output, out.error⟩

/-- The code of the account at `target`, in the block state `block`. -/
def codeAt (block : BlockState) (target : Address) : Except EvmError ByteArray :=
  let state := TransactionState.ofBlock block
  (state.getCode (state.getAccount target).codeHash).mapError .state

/-- Make a system call that must succeed, to `target` with the data `data`.

The block is invalid when `target` has no code, or when the call fails. -/
def checkedSystemCall {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (target : Address) (data : ByteArray) : Except BlockError SystemCallOutput := do
  let code ← (codeAt block target).mapError .aborted
  if code.size = 0 then throw (.systemContractEmpty target)
  let out ← (systemCall env block target data).mapError .aborted
  match out.error with
  | some error => throw (.systemCallFailed target error)
  | none => return out

/-! ## The calls of a block -/

/-- The system calls at the start of a block at `fork`, before its transactions.

From Dencun, the beacon roots contract stores the root of the parent beacon block.

From Pectra, the history storage contract then stores `parentHash`, the hash of the parent. -/
def startSystemCalls {fork : Fork} (env : BlockEnvironment fork) (parentHash : Hash32)
    (block : BlockState) : Except EvmError BlockState := do
  let block ← if h : .dencun ≤ fork then
      (·.block) <$> systemCall env block BEACON_ROOTS_ADDRESS
        ⟨(env.parentBeaconBlockRoot h).toArray⟩
    else pure block
  if .pectra ≤ fork then
    (·.block) <$> systemCall env block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
  else pure block

/-- The contracts that a block reads requests from, each with the type of its requests. -/
def REQUEST_CONTRACTS : List (UInt8 × Address) :=
  [(WITHDRAWAL_REQUEST_TYPE, WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS),
    (CONSOLIDATION_REQUEST_TYPE, CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)]

/-- The request list of type `type` with the data `data`, or none when the data is empty. -/
def requestList (type : UInt8) (data : ByteArray) : List ByteArray :=
  if data.size = 0 then [] else [⟨#[type]⟩ ++ data]

/-- The withdrawal and consolidation requests of a block at `fork`, after its withdrawals.

From Pectra, each contract returns the data of its requests, which follow its type byte.

A list with no data is left out.

Before Pectra, there is no request. -/
def readRequests {fork : Fork} (env : BlockEnvironment fork) (block : BlockState) :
    Except BlockError (BlockState × List ByteArray) :=
  if .pectra ≤ fork then
    REQUEST_CONTRACTS.foldlM
      (fun (block, requests) (type, target) => do
        let out ← checkedSystemCall env block target .empty
        return (out.block, requests ++ requestList type out.output))
      (block, [])
  else .ok (block, [])

end EthLib.Execution.Blocks
