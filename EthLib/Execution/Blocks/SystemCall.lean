module

public import EthLib.Execution.Blocks.AccessListBuilder
public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Transactions.Process

/-!
# `Blocks.SystemCall`

The calls that a block makes to system contracts, outside any transaction.

Each EIP states its call in its section on block processing or on the system call:

- [EIP-4788][eip-4788], the beacon roots contract
- [EIP-2935][eip-2935], the history storage contract
- [EIP-7002][eip-7002], the withdrawal request contract
- [EIP-7251][eip-7251], the consolidation request contract
- [EIP-8282][eip-8282], the builder deposit and exit contracts, in Last Call
- [EIP-8037][eip-8037], the reservoir of state gas, in Last Call

[eip-4788]: https://eips.ethereum.org/EIPS/eip-4788#block-processing
[eip-2935]: https://eips.ethereum.org/EIPS/eip-2935#block-processing
[eip-7002]: https://eips.ethereum.org/EIPS/eip-7002#system-call
[eip-7251]: https://eips.ethereum.org/EIPS/eip-7251#system-call
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#system-contracts-and-system-transactions
[eip-8282]: https://eips.ethereum.org/EIPS/eip-8282#request-queue-and-system-call
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)
open EthLib.Execution.Transactions (processMessageCall startAccessedAddressesOf)

/-! ## Addresses and gas -/

/-- The gas of a system call. -/
def SYSTEM_TRANSACTION_GAS : Nat := 30000000

/-- The reservoir of state gas of a system call at `fork`.

From Glamsterdam, it is the state gas of 16 new storage slots, 1,566,720.

Before Glamsterdam, it is 0. -/
def systemReservoir (fork : Fork) : Nat :=
  (gasSchedule fork).SYSTEM_RESERVOIR

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

/-- The builder deposit contract of EIP-8282. -/
def BUILDER_DEPOSIT_CONTRACT_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0x0000bFF46984e3725691FA540a8C7589300D8282)

/-- The builder exit contract of EIP-8282. -/
def BUILDER_EXIT_CONTRACT_ADDRESS : Address :=
  toAddressMasked (BitVec.ofNat 256 0x000064D678505ad48F8cCb093BC65613800E8282)

/-! ## The call -/

/-- What a system call leaves. -/
structure SystemCallOutput where
  /-- The state of the call once it has run, before its writes join the block. -/
  state : TransactionState
  /-- The data that the call returned. -/
  output : ByteArray
  /-- The error that stopped the call, or none when it succeeded. -/
  error : Option EvmError

/-- The block state, with the writes of the call. -/
def SystemCallOutput.block (output : SystemCallOutput) : BlockState :=
  output.state.incorporateTxIntoBlock.parent

/-- The message of a system call to `target` with the data `data`, at `fork`.

It comes from the system address, with 30,000,000 gas and no value.

Its code is empty until the call reads the code of `target`. -/
def systemMessage {fork : Fork} (env : BlockEnvironment fork) (target : Address)
    (data : ByteArray) : Message fork where
  blockEnv := env
  -- EIP-4788: the call runs as `SYSTEM_ADDRESS`.
  --
  -- The price per gas is the base fee, which no EIP states.
  txEnv := { origin := SYSTEM_ADDRESS
             gasPrice := if h : .london ≤ fork then env.baseFeePerGas h else 0
             blobVersionedHashes := fun _ => [] }
  caller := SYSTEM_ADDRESS
  target := some target
  currentTarget := target
  -- EIP-4788: a gas limit of 30000000; EIP-2935, EIP-7002, EIP-7251 and EIP-8282 agree.
  --
  -- This gas does not count against the gas limit of the block, and nobody pays for it.
  --
  -- So the call adds to neither gas count of the block.
  gas := SYSTEM_TRANSACTION_GAS
  -- EIP-8037: from Glamsterdam, the extra state gas goes to the state gas reservoir.
  --
  -- That reservoir holds the state gas of 16 new storage slots.
  reservoir := systemReservoir fork
  -- EIP-4788: a value of 0.
  value := 0
  data := data
  codeAddress := some target
  code := .empty
  depth := 0
  shouldTransferValue := false
  isStatic := false
  disablePrecompiles := false

/-- The substate of a system call to `target` when its message starts, at `fork`.

Up to BPO5, no address starts accessed.

From Glamsterdam, the call starts as a transaction from the system address with no access list. -/
def systemSubstate {fork : Fork} (env : BlockEnvironment fork) (target : Address) : Substate :=
  -- No EIP states which addresses a system call starts with accessed.
  --
  -- From Glamsterdam, the call starts as the first frame of a transaction with no access list.
  --
  -- No storage key starts accessed.
  { Substate.empty with
    accessedAddresses := if fork ≥ .glamsterdam then
        -- The beneficiary, the precompiles, the system address and `target` start accessed.
        startAccessedAddressesOf fork env.coinbase SYSTEM_ADDRESS target []
      -- Up to BPO5, no address starts accessed.
      else ∅ }

/-- Make a system call to `target` with the data `data`, on the block state `block` at `fork`.

A call that fails leaves the block state as it was.

It fails only with an error that aborts the whole execution, such as missing code.

It has no receipt, so its logs enter no receipt. -/
def systemCall {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (target : Address) (data : ByteArray) : Except EvmError SystemCallOutput := do
  let message := systemMessage env target data
  let state := TransactionState.ofBlock block
  -- The call runs as the message of a transaction, from the accesses of its start.
  --
  -- EIP-2935: the history storage account and its slots stay cold for every later transaction.
  --
  -- The accesses of the call end with it, since its output keeps no substate.
  let substate := systemSubstate env target
  -- Up to BPO5, the gas meter is one counter of the gas left.
  --
  -- From Glamsterdam, the meter of EIP-8037 also meters state gas.
  let out ← if fork ≥ .glamsterdam then
      processMessageCall (Meter := StateGasMeter) env.chainId.toNat message state substate
    else processMessageCall (Meter := Nat) env.chainId.toNat message state substate
  return ⟨out.state, out.output, out.error⟩

/-- The code of the account at `target`, in the block state `block`. -/
def codeAt (block : BlockState) (target : Address) : Except EvmError ByteArray :=
  let state := TransactionState.ofBlock block
  (state.getCode (state.getAccount target).codeHash).mapError .state

/-- Make a system call that must succeed, to `target` with the data `data`.

The block is invalid when the contract has no code or the call fails. -/
def checkedSystemCall {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (target : Address) (data : ByteArray) : Except BlockError SystemCallOutput := do
  let code ← (codeAt block target).mapError .aborted
  -- EIP-7002: a block whose request contract has no code is invalid.
  --
  -- EIP-7251 says the same; EIP-8282 says it of either of its contracts.
  if code.size = 0 then throw (.systemContractEmpty target)
  let out ← (systemCall env block target data).mapError .aborted
  -- EIP-7002 and EIP-7251: a call that fails or returns an error makes the block invalid.
  --
  -- EIP-8282: a failed system call to either of its contracts makes the block invalid.
  match out.error with
  | some error => throw (.systemCallFailed target error)
  | none => return out

/-! ## The body of a block -/

/-- The block state, and the builder of the block access list, as the body of a block runs. -/
structure BodyState where
  /-- The block state, with the writes so far. -/
  block : BlockState
  /-- The builder of the block access list. -/
  builder : AccessListBuilder

/-- The body before it runs, on the block state `block`, at position 0. -/
def BodyState.init (block : BlockState) : BodyState := ⟨block, .init block⟩

/-- Begin the position `index` of the body, from the block state so far. -/
def BodyState.beginIndex (body : BodyState) (index : Nat) : BodyState :=
  -- From Fusaka, no position of a checked block wraps in this conversion to 32 bits.
  { body with builder := body.builder.beginIndex (UInt32.ofNat index) body.block }

/-- The body once a call that ends with the state `tx` joins it.

The builder records the call, then its writes join the block. -/
def BodyState.join (body : BodyState) (tx : TransactionState) :
    Except State.StateError BodyState := do
  let builder ← body.builder.recordTransaction tx
  return ⟨tx.incorporateTxIntoBlock.parent, builder⟩

/-! ## The calls of a block -/

/-- The system calls at the start of a block at `fork`, before its transactions.

From Dencun, the beacon roots contract stores the root of the parent beacon block.

From Pectra, the history storage contract then stores `parentHash`, the hash of the parent.

These two calls are unchecked: the block goes on when the contract has no code or the call fails. -/
def startSystemCalls {fork : Fork} (env : BlockEnvironment fork) (parentHash : Hash32)
    (body : BodyState) : Except EvmError BodyState := do
  -- Each call joins the body at the current position.
  --
  -- EIP-4788, from Dencun: a call to `BEACON_ROOTS_ADDRESS` as `SYSTEM_ADDRESS`.
  --
  -- Its input is the 32 bytes of the root of the parent beacon block.
  --
  -- Without code at `BEACON_ROOTS_ADDRESS`, the call fails silently: no check here.
  let body ← if h : .dencun ≤ fork then do
      let out ← systemCall env body.block BEACON_ROOTS_ADDRESS
        ⟨(env.parentBeaconBlockRoot h).toArray⟩
      (body.join out.state).mapError .state
    else pure body
  -- EIP-2935, from Pectra: a call to `HISTORY_STORAGE_ADDRESS` as `SYSTEM_ADDRESS`.
  --
  -- Its input is the 32 bytes of the hash of the parent block.
  --
  -- As for the beacon roots, a missing contract makes the call fail silently: no check here.
  if .pectra ≤ fork then do
    let out ← systemCall env body.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
    (body.join out.state).mapError .state
  else pure body

/-- The request contracts of Pectra, each with the type of its requests. -/
def REQUEST_CONTRACTS : List (UInt8 × Address) :=
  [(WITHDRAWAL_REQUEST_TYPE, WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS),
    (CONSOLIDATION_REQUEST_TYPE, CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)]

/-- The contracts of the builder requests, which a block reads from Glamsterdam. -/
def BUILDER_REQUEST_CONTRACTS : List (UInt8 × Address) :=
  [(BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_DEPOSIT_CONTRACT_ADDRESS),
    (BUILDER_EXIT_REQUEST_TYPE, BUILDER_EXIT_CONTRACT_ADDRESS)]

/-- The contracts that a block at `fork` reads requests from, in the order of their types.

From Glamsterdam, the builder contracts come after the consolidation contract. -/
def requestContracts (fork : Fork) : List (UInt8 × Address) :=
  if fork ≥ .glamsterdam then REQUEST_CONTRACTS ++ BUILDER_REQUEST_CONTRACTS
  else REQUEST_CONTRACTS

/-- The request list of type `type` with the data `data`, or none when the data is empty.

A list with no data is left out, as [EIP-7685][eip-7685] leaves it out of its hash.

[eip-7685]: https://eips.ethereum.org/EIPS/eip-7685#block-header -/
def requestList (type : UInt8) (data : ByteArray) : List ByteArray :=
  -- EIP-7685: a request list is its type byte, then its data.
  --
  -- An empty list is dropped here.
  --
  -- EIP-7685 leaves a list of only 1 byte out of the hash.
  if data.size = 0 then [] else [⟨#[type]⟩ ++ data]

/-- Call a request contract after the body and the requests so far, and add its requests.

The contract comes with the type of its requests, which starts each of them.

The call joins the body at the current position, and its requests follow those read so far. -/
def readRequest {fork : Fork} (env : BlockEnvironment fork)
    (state : BodyState × List ByteArray) (contract : UInt8 × Address) :
    Except BlockError (BodyState × List ByteArray) := do
  -- EIP-7002: a call to `WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS` as `SYSTEM_ADDRESS`, with no data.
  --
  -- EIP-7251 and EIP-8282 call their contracts the same way.
  let out ← checkedSystemCall env state.1.block contract.2 .empty
  let body ← (state.1.join out.state).mapError .state
  -- EIP-7002: the requests come in the exact order in which the contract dequeues them.
  --
  -- EIP-7251 and EIP-8282 say the same of their queues.
  --
  -- From Pectra, each contract returns the data of its requests, which follow its type byte.
  return (body, state.2 ++ requestList contract.1 out.output)

/-- The withdrawal and consolidation requests of a block at `fork`, after its withdrawals.

From Glamsterdam, the builder deposit and exit requests follow them.

Before Pectra, there is no request. -/
def readRequests {fork : Fork} (env : BlockEnvironment fork) (body : BodyState) :
    Except BlockError (BodyState × List ByteArray) :=
  if .pectra ≤ fork then
    -- EIP-7002 and EIP-7251: at the end of each execution block, one call per contract.
    --
    -- EIP-7685: the lists come by ascending request type.
    --
    -- Each call joins the body at the current position.
    (requestContracts fork).foldlM (readRequest env) (body, [])
  else .ok (body, [])

end EthLib.Execution.Blocks
