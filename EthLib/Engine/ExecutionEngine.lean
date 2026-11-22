module

public import EthLib.Consensus.Transition.Execution
public import EthLib.Engine.NewPayload

/-!
# `Engine.ExecutionEngine`

The execution layer of the beacon chain, built from the checks of `engine_newPayload`.

The beacon chain calls one version of the method at each of its forks.

The execution layer reads the payload at its own active fork, which that version must take.

The Engine API states the forks that each version takes, and EthLib picks the version from them.

A step comment names the version of the method, as in version 3, step 3.

The Engine API calls the execution side of Glamsterdam by the name Amsterdam.

It calls that of Hegotá by the name Bogota.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`engine_newPayloadV1`][v1], and the [payload validation][validation] of Paris
- [`engine_newPayloadV2`][v2]
- [`engine_newPayloadV3`][v3]
- [`engine_newPayloadV4`][v4], and its update by Amsterdam in [`amsterdam.md`][v4-amsterdam]
- [`engine_newPayloadV5`][v5]
- [`engine_newPayloadV6`][v6], at commit `68d76a5`, where a list entry may be any byte string

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_newpayloadv1
[validation]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-validation
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_newpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_newpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#engine_newpayloadv4
[v4-amsterdam]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#update-the-methods-of-previous-forks
[v5]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_newpayloadv5
[v6]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/engine/bogota.md#engine_newpayloadv6
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Block BlockChain stateTransition)
open EthLib.Execution.Transactions (Transaction)
open EthLib.Engine.Json (AnyPayload)

variable {preset : Consensus.Preset} {fork : Fork}

/-- The version of the method that the beacon chain calls at a fork, or 0 for none. -/
def newPayloadVersion (fork : Fork) : Nat :=
  -- Heze calls version 6, which takes the payloads of Bogota and an inclusion list.
  if .hegota ≤ fork then 6
  -- Gloas calls version 5, which takes the payloads of Amsterdam.
  else if .glamsterdam ≤ fork then 5
  -- From Electra, Fulu included, up to Gloas: version 4, which takes Prague to Amsterdam, excluded.
  else if .pectra ≤ fork then 4
  -- Deneb calls version 3, which takes the payloads of Cancun.
  else if .dencun ≤ fork then 3
  -- Capella calls version 2, which takes the payloads of Shanghai.
  else if .shapella ≤ fork then 2
  -- Bellatrix calls version 1, which takes the payloads of Paris.
  else if .bellatrix ≤ fork then 1
  -- Before Bellatrix, the beacon chain has no payload.
  else 0

/-- A withdrawal of the beacon chain, as the execution layer reads it. -/
def executionWithdrawal (w : Consensus.Withdrawal) : Execution.Blocks.Withdrawal :=
  -- `WithdrawalV1`: `index`, `validatorIndex`, `address` and `amount`, in that order.
  ⟨w.index, w.validatorIndex, w.address, w.amount⟩

/-- The transactions of a payload of the beacon chain, as byte arrays in order. -/
def beaconTransactions (p : Consensus.ExecutionPayload preset fork) : List ByteArray :=
  -- `transactions`: an `Array of DATA`, each the bytes of one transaction.
  p.transactions.data.toList.map fun tx => ⟨tx.data⟩

/-- A payload of the beacon chain as the structure of the Engine API, with the fields of its fork.

It has none when the logs Bloom filter of the preset does not have 256 bytes. -/
def anyPayloadOf (p : Consensus.ExecutionPayload preset fork) : Option AnyPayload :=
  -- `ExecutionPayloadV1`: `logsBloom` is `DATA` of 256 bytes.
  if bloom : preset.BYTES_PER_LOGS_BLOOM.toNat = 256 then
    some {
      -- `ExecutionPayloadV3` from Deneb, `ExecutionPayloadV2` from Capella, else version 1.
      version := if .dencun ≤ fork then 3 else if .shapella ≤ fork then 2 else 1
      common := {
        parentHash := p.parentHash, feeRecipient := p.feeRecipient, stateRoot := p.stateRoot,
        receiptsRoot := p.receiptsRoot, logsBloom := p.logsBloom.cast bloom
        prevRandao := p.prevRandao, blockNumber := p.blockNumber, gasLimit := p.gasLimit
        gasUsed := p.gasUsed, timestamp := p.timestamp, extraData := ⟨p.extraData.data⟩
        baseFeePerGas := p.baseFeePerGas, blockHash := p.blockHash
        transactions := beaconTransactions p
        withdrawals := fun h => absurd h (by decide)
        blobGasUsed := fun h => absurd h (by decide)
        excessBlobGas := fun h => absurd h (by decide) }
      -- Version 2 of the structure appends `withdrawals`.
      withdrawals := (sinceValue p.withdrawals).map fun ws => ws.data.toList.map executionWithdrawal
      -- Version 3 appends `blobGasUsed` and `excessBlobGas`.
      blobGasUsed := sinceValue p.blobGasUsed
      excessBlobGas := sinceValue p.excessBlobGas }
  else none

/-- The JSON parameters of a payload request, for the method the beacon chain calls at its fork.

It has none when the logs Bloom filter of the preset does not have 256 bytes.

It also has none when the request lists cannot be made.

From Heze the caller gives the transactions of the inclusion list, from the slot before.

It has none before Bellatrix, where the beacon chain calls no version. -/
def newPayloadRequestJson (r : Consensus.NewPayloadRequest preset fork)
    (inclusionList : Since .hegota fork (List ByteArray)) : Option Lean.Json := do
  -- Before Bellatrix there is no version to call, so no request.
  guard (newPayloadVersion fork ≠ 0)
  let p := r.executionPayload
  let any ← anyPayloadOf p
  -- Parameter 1: version 3 of the structure from Deneb, version 2 from Capella, else version 1.
  let shape : Fork := if .dencun ≤ fork then .dencun else if .shapella ≤ fork then .shapella
    else .paris
  let payload ← (any.atFork shape).toOption
  -- Parameter 4, from Electra: `executionRequests`, the request lists of EIP-7685.
  let requests ← r.requestsList.toOption
  -- From Gloas, parameter 1 is `ExecutionPayloadV4`, which appends these two fields.
  --
  -- `blockAccessList`, the bytes of the list, and `slotNumber`, a 64-bit quantity.
  let amsterdam := do
    let accessList ← sinceValue p.blockAccessList
    let slot ← sinceValue p.slotNumber
    pure (ByteArray.mk accessList.data, slot)
  -- Parameter 2, from Deneb: `expectedBlobVersionedHashes`.
  --
  -- The default for an earlier fork is never written, since versions 1 and 2 omit it.
  let hashes := ((sinceValue r.versionedHashes).map (·.data.toList)).getD []
  -- Parameter 3, from Deneb: `parentBeaconBlockRoot`, with the same unwritten default.
  let root := (sinceValue r.parentBeaconBlockRoot).getD 0
  match sinceValue inclusionList, amsterdam with
  -- Version 6, from Heze: parameter 5, `inclusionListTransactions`, follows the four others.
  | some list, some fields =>
    return newPayloadV6ParamsJson payload fields hashes root ((sinceValue requests).getD []) list
  -- Versions 1 to 5: the parameters of the version, in order.
  | _, _ =>
    return newPayloadParamsJson (newPayloadVersion fork) payload amsterdam hashes root
      ((sinceValue requests).getD [])

/-- The block of a payload of the beacon chain, at the active fork of a chain configuration.

It has none when one of the checks of the method before the state transition fails. -/
def payloadBlock (config : ChainConfig) (p : Consensus.ExecutionPayload preset fork)
    (parentBeaconBlockRoot : Since .dencun fork Consensus.Root)
    (requests : Since .pectra fork (List ByteArray)) :
    Option ((f : Fork) × Block f Transaction) := do
  let any ← anyPayloadOf p
  -- The fork of the payload: the active fork at its number and its timestamp.
  let executionFork ← config.activeFork p.blockNumber.toNat p.timestamp.toNat
  -- The version takes the fork of the payload: version 3, step 2, and step 1 of versions 4 to 6.
  --
  -- Versions 1 and 2 take the forks that the check of the method gives them.
  --
  -- Otherwise the method answers `-38005`, unsupported fork, so there is no block.
  if acceptsFork (newPayloadVersion fork) executionFork then
    -- Version 3, step 1: the payload has exactly the fields of the structure of that fork.
    let payload ← (any.atFork executionFork).toOption
    -- Step 1 again: `parentBeaconBlockRoot` exactly from Cancun, here Dencun.
    let beacon ← (Json.since (f := .dencun) "parentBeaconBlockRoot"
      (sinceValue parentBeaconBlockRoot)).toOption
    -- Version 4, parameter 4: `executionRequests` exactly from Prague, here Pectra.
    let lists ← (Json.since (f := .pectra) "executionRequests" (sinceValue requests)).toOption
    -- Version 5, step 2: a missing `blockAccessList` is `-32602`, from Amsterdam, here Glamsterdam.
    --
    -- By version 3, step 1, so is one present before Amsterdam.
    let accessList ← (Json.since (f := .glamsterdam) "blockAccessList"
      ((sinceValue p.blockAccessList).map fun list => ⟨list.data⟩)).toOption
    -- `slotNumber` exactly from Amsterdam, by the strict match of version 3, step 1.
    let slot ← (Json.since (f := .glamsterdam) "slotNumber" (sinceValue p.slotNumber)).toOption
    -- Version 1, step 1: each transaction has at least one byte.
    --
    -- Step 6: an invalid entry is `INVALID` too, so each transaction decodes.
    --
    -- Step 2: the block hash of the payload is `Keccak256(RLP(ExecutionBlockHeader))`.
    --
    -- Version 4, step 2: that header holds the commitment to the request lists.
    --
    -- Version 5, step 3: the block access list decodes as RLP.
    --
    -- EIP-7928 puts its hash in the header, and EIP-7843 puts the slot number there.
    let block ← (payload.toBlock beacon lists accessList slot).toOption
    return ⟨executionFork, block⟩
  else none

/-- The execution layer of the beacon chain, on a chain of the execution layer.

Each of its checks reads the block of the payload at the active fork of the chain.

The answer to a payload request is the default answer from its three checks. -/
def executionEngine (chain : BlockChain) : Consensus.ExecutionEngine preset fork where
  -- The block hash is valid when the payload passes the checks before the state transition.
  isValidBlockHash p root requests := (payloadBlock chain.config p root requests).isSome
  isValidVersionedHashes request :=
    match request.requestsList with
    | .ok requests =>
      match payloadBlock chain.config request.executionPayload request.parentBeaconBlockRoot
          requests with
      | some ⟨_, block⟩ =>
        -- Version 3, step 3.1: the actual array joins the versioned hashes of blob transactions.
        --
        -- They come in the order of inclusion.
        --
        -- Without a blob transaction, step 3.1 requires an expected array of `[]`.
        --
        -- Step 3.2: the expected and the actual arrays match.
        --
        -- Before Deneb there is no expected array, so nothing to check.
        (sinceValue request.versionedHashes).all fun hashes =>
          ExecutionPayload.blobVersionedHashes block.transactions == hashes.data.toList
      -- A payload without a block has no valid versioned hashes.
      | none => false
    -- Request lists that cannot be made give no valid versioned hashes.
    | .error _ => false
  notifyNewPayload p root requests :=
    match payloadBlock chain.config p root requests with
    -- Payload validation, step 3: the block passes the rule sets of the header and of execution.
    --
    -- Not run here: step 2, the check of the terminal proof-of-work block, which the method runs.
    --
    -- The seal of proof of work is left out, as the block validity of EIP-3675 removes it.
    | some ⟨_, block⟩ => (stateTransition chain block (checkSeal := false)).toBool
    | none => false

end EthLib.Engine
