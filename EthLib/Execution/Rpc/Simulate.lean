module

public import EthLib.Execution.Rpc.Call
public import EthLib.Execution.Rpc.Json

/-!
# `Execution.Rpc.Simulate`

The request of `eth_simulateV1` of [`execute.yaml`][method], and its checks before the execution.

The method runs calls in a sequence of blocks on top of a base block, `latest` by default.

The [schemas][schema], the [notes][notes] and the fixtures fix the request and its codes.

[method]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/execute.yaml
[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/execute.yaml
[notes]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/docs-api/docs/ethsimulatev1-notes.mdx
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Execution.State (State Account EMPTY_ACCOUNT)
open EthLib.Execution.Transactions (precompileAddresses)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The request -/

/-- The fields of the header of a simulated block that a request overrides. -/
structure BlockOverrides where
  /-- The number of the block. -/
  number : Option Nat := none
  /-- The randomness of the beacon chain. -/
  prevRandao : Option Bytes32 := none
  /-- The time of the block. -/
  time : Option Nat := none
  /-- The gas limit of the block. -/
  gasLimit : Option Nat := none
  /-- The recipient of the priority fees. -/
  feeRecipient : Option Address := none
  /-- The base fee per gas. -/
  baseFeePerGas : Option U256 := none
  /-- The withdrawals of the block. -/
  withdrawals : Option (List Withdrawal) := none
  /-- The base fee per blob gas. -/
  blobBaseFee : Option Nat := none

/-- The new storage of an account: every slot, or only some slots. -/
inductive StorageOverride where
  /-- The whole storage: these slots, and zero everywhere else. -/
  | full (slots : List (Bytes32 × U256))
  /-- These slots, and the other slots unchanged. -/
  | diff (slots : List (Bytes32 × U256))

/-- The override of an account. -/
structure AccountOverride where
  /-- The nonce of the account. -/
  nonce : Option Nat := none
  /-- The balance of the account. -/
  balance : Option U256 := none
  /-- The code of the account. -/
  code : Option ByteArray := none
  /-- The address that receives the precompile at this address. -/
  movePrecompileToAddress : Option Address := none
  /-- The storage of the account, from `state` or `stateDiff`. -/
  storage : Option StorageOverride := none

/-- One block of the request: its overrides and its calls. -/
structure BlockStateCall where
  /-- The fields of the header that the request overrides. -/
  blockOverrides : BlockOverrides := {}
  /-- The accounts that the request overrides, each address at most once. -/
  stateOverrides : List (Address × AccountOverride) := []
  /-- The calls of the block. -/
  calls : List GenericTransaction := []

/-- The first parameter of the method. -/
structure SimulatePayload where
  /-- The blocks to simulate. -/
  blockStateCalls : List BlockStateCall
  /-- Whether ether transfers are added to the logs. -/
  traceTransfers : Bool := false
  /-- Whether the calls are validated as transactions of a block. -/
  validation : Bool := false
  /-- Whether the blocks carry full transactions rather than their hashes. -/
  returnFullTransactions : Bool := false

/-- The keys of the schema of block overrides. -/
def blockOverrideKeys : List String :=
  ["number", "prevRandao", "time", "gasLimit", "feeRecipient", "baseFeePerGas", "withdrawals",
    "blobBaseFee"]

/-- The keys of the schema of an account override. -/
def accountOverrideKeys : List String :=
  ["nonce", "balance", "code", "movePrecompileToAddress", "state", "stateDiff"]

/-- An object of the request that holds only the given keys, or why it does not. -/
def onlyKeys (what : String) (keys : List String) (j : Json) : Read Unit := do
  let .obj kvs := j | reject s!"{what}: not an object"
  match kvs.toList.find? fun (name, _) => !keys.contains name with
  | some (name, _) => reject s!"{what}: unknown key {name}"
  | none => pure ()

/-- Block overrides, with only the keys of their schema. -/
def blockOverrides (j : Json) : Read BlockOverrides := do
  onlyKeys "blockOverrides" blockOverrideKeys j
  let fs ← fields "blockOverrides" j
  let opt {α : Type} (name : String) (f : String → Json → Read α) : Read (Option α) :=
    (fs.lookup name).mapM (f name)
  return {
    number := ← opt "number" fun what => quantity what 64
    prevRandao := ← opt "prevRandao" bytes32
    time := ← opt "time" fun what => quantity what 64
    gasLimit := ← opt "gasLimit" fun what => quantity what 64
    feeRecipient := ← opt "feeRecipient" address
    baseFeePerGas := ← opt "baseFeePerGas" uint256
    withdrawals := ← opt "withdrawals" fun what => array what withdrawal
    blobBaseFee := ← opt "blobBaseFee" fun what => quantity what 64 }

/-- The slots of a storage override: each 32-byte key with its word, and no key twice. -/
def storageSlots (what : String) (j : Json) : Read (List (Bytes32 × U256)) := do
  let .obj kvs := j | reject s!"{what}: not an object"
  let slots ← kvs.toList.mapM fun (key, value) => do
    let key ← fixed "slot" 32 (.str key) (upper := true)
    return (key, U256.fromBeBytes (← hash32 "slot value" value))
  unless (slots.map (·.1)).Nodup do reject s!"{what}: a slot twice"
  return slots

/-- Whether an object has a key, whatever its value, `null` included. -/
def hasKey (j : Json) (name : String) : Bool :=
  match j with
  | .obj kvs => kvs.toList.any (·.1 == name)
  | _ => false

/-- An account override, with only the keys of its schema, and not both `state` and `stateDiff`.

The two keys are rejected together even when one of them is `null`, as the schema does. -/
def accountOverride (j : Json) : Read AccountOverride := do
  onlyKeys "account override" accountOverrideKeys j
  if hasKey j "state" && hasKey j "stateDiff" then
    reject "account override: both state and stateDiff"
  let fs ← fields "account override" j
  let opt {α : Type} (name : String) (f : String → Json → Read α) : Read (Option α) :=
    (fs.lookup name).mapM (f name)
  let full ← opt "state" storageSlots
  let diff ← opt "stateDiff" storageSlots
  let storage := match full, diff with
    | some slots, _ => some (StorageOverride.full slots)
    | none, some slots => some (StorageOverride.diff slots)
    | none, none => none
  return {
    nonce := ← opt "nonce" fun what => quantity what 64
    balance := ← opt "balance" uint256
    code := ← opt "code" bytes
    movePrecompileToAddress := ← opt "movePrecompileToAddress" address
    storage }

/-- The account overrides of a block, by address, with no address twice. -/
def stateOverrides (j : Json) : Read (List (Address × AccountOverride)) := do
  let .obj kvs := j | reject "stateOverrides: not an object"
  let overrides ← kvs.toList.mapM fun (name, value) => do
    return (← address "address" (.str name), ← accountOverride value)
  unless (overrides.map (·.1)).Nodup do reject "stateOverrides: an address twice"
  return overrides

/-- One block of the request. -/
def blockStateCall (j : Json) : Read BlockStateCall := do
  let fs ← fields "block state call" j
  return {
    blockOverrides := ← ((fs.lookup "blockOverrides").mapM blockOverrides).map (·.getD {})
    stateOverrides := ← ((fs.lookup "stateOverrides").mapM stateOverrides).map (·.getD [])
    calls := ← ((fs.lookup "calls").mapM (array "calls" genericTransaction)).map (·.getD []) }

/-- The first parameter of the method, with each flag `false` when absent. -/
def simulatePayload (j : Json) : Read SimulatePayload := do
  let fs ← fields "payload" j
  let flag (name : String) : Read Bool := ((fs.lookup name).mapM (bool name)).map (·.getD false)
  return {
    blockStateCalls := ← array "blockStateCalls" blockStateCall (← field "payload" fs
      "blockStateCalls")
    traceTransfers := ← flag "traceTransfers"
    validation := ← flag "validation"
    returnFullTransactions := ← flag "returnFullTransactions" }

/-! ## The defaults of a call -/

namespace GenericTransaction

/-- The type of a call of a simulation: its own, else type 2, as the notes say.

It replaces the kind that a call infers from its fields, which reads a blob fee cap as type 3.

Blob hashes make type 3, as the fixtures show, and a blob fee cap alone does not.

The source is silent on the other kinds, which type 2 cannot carry.

So EthLib makes authorizations type 4, and a gas price type 0, or type 1 with an access list. -/
def simulateType (tx : GenericTransaction) : UInt8 :=
  match tx.type with
  | some t => t
  | none =>
    if tx.authorizationList.any (!·.isEmpty) then 4
    else if tx.blobVersionedHashes.any (!·.isEmpty) then 3
    else if tx.gasPrice.isSome then if tx.accessList.isSome then 1 else 0
    else 2

/-- A call of a simulation with its defaults filled in.

The nonce is that of the sender, its default included, after the earlier calls.

The gas is what the block has left.

The sender is the zero address, as the notes say.

The other fields keep their defaults of a call: no value, no data and no fee. -/
def withDefaults (tx : GenericTransaction) (nonce gas : Nat) : GenericTransaction :=
  { tx with
    type := some tx.simulateType
    nonce := some (tx.nonce.getD nonce)
    gas := some (tx.gas.getD gas)
    sender := some (tx.sender.getD (Vector.replicate 20 0)) }

end GenericTransaction

/-! ## The sequence of blocks -/

/-- The choices that the source leaves to the node, for a simulation. -/
structure SimulateChoices where
  /-- The seconds from a block to the next one, when the request gives no time. -/
  blockTime : Nat := 12
  /-- The block time is positive, so the gap blocks have increasing times. -/
  blockTime_pos : 0 < blockTime := by decide
  /-- The most blocks of a simulation, gap blocks included. -/
  maxBlocks : Nat := 256

/-- A block of the request, with its number, its time and the empty blocks before it. -/
structure PlannedBlock where
  /-- The number of empty blocks that fill the gap before it. -/
  gap : Nat
  /-- The number of the block. -/
  number : Nat
  /-- The time of the block. -/
  time : Nat
  /-- The block of the request. -/
  request : BlockStateCall

/-- The blocks of the request after a block of the given number and time.

A number above the next one leaves a gap, which empty blocks fill a block time apart. -/
def planBlocks (blockTime number time : Nat) : List BlockStateCall → List PlannedBlock
  | [] => []
  | c :: cs =>
    let n := c.blockOverrides.number.getD (number + 1)
    let gap := n - (number + 1)
    let t := c.blockOverrides.time.getD (time + blockTime * (gap + 1))
    ⟨gap, n, t, c⟩ :: planBlocks blockTime n t cs

/-- The number and the time of every block of a plan, gap blocks included. -/
def expandBlocks (blockTime number time : Nat) : List PlannedBlock → List (Nat × Nat)
  | [] => []
  | b :: bs =>
    (List.range b.gap).map (fun i => (number + 1 + i, time + blockTime * (i + 1))) ++
      (b.number, b.time) :: expandBlocks blockTime b.number b.time bs

/-- The number of blocks of a plan, gap blocks included. -/
def PlannedBlock.count (bs : List PlannedBlock) : Nat :=
  (bs.map (·.gap + 1)).sum

/-- The code of block numbers that do not increase. -/
def blockNumberOrder : ErrorCode := ⟨-38020, "Block number in sequence did not increase"⟩

/-- The code of block times that do not increase. -/
def blockTimeOrder : ErrorCode :=
  ⟨-38021, "Block timestamp in sequence did not increase or stay the same"⟩

/-- The code of a precompile moved to its own address. -/
def movePrecompileToItself : ErrorCode :=
  ⟨-38022, "MovePrecompileToAddress referenced itself in replacement"⟩

/-- The code of a limit of the node that the request exceeds. -/
def clientLimitExceeded : ErrorCode := ⟨-38026, "Client adjustable limit exceeded"⟩

/-- Check that the numbers and the times of a plan strictly increase, gap blocks included.

The plan follows a block of the given number and time. -/
def checkOrder (blockTime number time : Nat) : List PlannedBlock → Except RpcError Unit
  | [] => .ok ()
  | b :: bs => do
    ensure (number < b.number)
      (blockNumberOrder.toRpcError (some (.str s!"{b.number} <= {number}")))
    let before := time + blockTime * b.gap
    ensure (before < b.time) (blockTimeOrder.toRpcError (some (.str s!"{b.time} <= {before}")))
    checkOrder blockTime b.number b.time bs

/-! ## The overrides of the state -/

/-- Whether an account override changes the state, which a move alone does not. -/
def AccountOverride.changesState (o : AccountOverride) : Bool :=
  o.nonce.isSome || o.balance.isSome || o.code.isSome || o.storage.isSome

/-- The storage of an account after an override of its slots. -/
def StorageOverride.apply (storage : Std.ExtTreeMap Bytes32 U256) :
    StorageOverride → Std.ExtTreeMap Bytes32 U256
  | .full slots => slots.foldl (fun m (k, v) => m.insert k v) ∅
  | .diff slots => slots.foldl (fun m (k, v) => m.insert k v) storage

/-- The state after the override of the account at an address.

An override that changes the state creates the account when it has none. -/
def applyAccountOverride (s : State) (a : Address) (o : AccountOverride) : State :=
  if o.changesState then
    let account := (s.getAccountOptional a).getD EMPTY_ACCOUNT
    let account := { account with
      nonce := o.nonce.getD account.nonce
      balance := o.balance.getD account.balance
      codeHash := (o.code.map keccak256).getD account.codeHash }
    { accounts := s.accounts.insert a account
      storage := match o.storage with
        | none => s.storage
        | some st => s.storage.insert a (st.apply (s.storage.getD a ∅))
      code := match o.code with
        | none => s.code
        | some c => s.code.insert (keccak256 c) c }
  else s

/-- The state after the overrides of a block. -/
def applyOverrides (s : State) (overrides : List (Address × AccountOverride)) : State :=
  overrides.foldl (fun s (a, o) => applyAccountOverride s a o) s

/-- The moves of precompiles of a block: each moved precompile with its new address. -/
def precompileMoves (overrides : List (Address × AccountOverride)) : List (Address × Address) :=
  overrides.filterMap fun (a, o) => o.movePrecompileToAddress.map (a, ·)

/-- Check the moves of precompiles of a block at a fork. -/
def checkMoves (fork : Fork) (overrides : List (Address × AccountOverride)) :
    Except RpcError Unit :=
  (precompileMoves overrides).forM fun (a, b) => do
    ensure (a ∈ precompileAddresses fork)
      (invalidInput.toRpcError (some (.str s!"account {hexString a.toList} is not a precompile")))
    ensure (a ≠ b) movePrecompileToItself.toRpcError

/-! ## The checks before the execution -/

/-- A simulation ready to run: its base block and its blocks, each with its fork. -/
structure SimulatePlan where
  /-- The block that the simulation starts after. -/
  base : BlockRecord
  /-- The blocks of the request, each with its fork. -/
  blocks : List (PlannedBlock × Fork)

/-- The plan of a simulation on top of the block that `p` names, or the error that stops it.

It checks the base block, the limit and the order, then the fork and the moves of each block. -/
def ChainView.planSimulate (v : ChainView) (payload : SimulatePayload) (p : BlockParam)
    (choices : SimulateChoices) : Except RpcError SimulatePlan := do
  let some base ← v.resolve p | throw (invalidInput.toRpcError (some (.str "header not found")))
  let number := base.block.header.number
  let time := base.block.header.timestamp.toNat
  let blocks := planBlocks choices.blockTime number time payload.blockStateCalls
  ensure (PlannedBlock.count blocks ≤ choices.maxBlocks)
    (clientLimitExceeded.toRpcError (some (.str "too many blocks")))
  checkOrder choices.blockTime number time blocks
  let blocks ← blocks.mapM fun b => do
    let some fork := v.config.activeFork b.number b.time
      | throw (callInternalError "no fork for the block")
    ensure (fork < .hegota) (callInternalError "fork not yet specified")
    checkMoves fork b.request.stateOverrides
    return (b, fork)
  return { base, blocks }

/-- The answer of `eth_simulateV1`, which fails once the request passes its checks.

The execution of the simulated blocks is not yet specified, so the node fails with `-32603`. -/
def ChainView.simulate (v : ChainView) (payload : SimulatePayload) (p : BlockParam)
    (choices : SimulateChoices) : Except RpcError Json := do
  let _ ← v.planSimulate payload p choices
  throw (callInternalError "simulated blocks are not yet specified")

end EthLib.Execution.Rpc
