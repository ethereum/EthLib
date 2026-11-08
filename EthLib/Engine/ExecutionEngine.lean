module

public import EthLib.Consensus.Transition.Execution
public import EthLib.Engine.NewPayload

/-!
# `Engine.ExecutionEngine`

The execution layer of the beacon chain, built from the checks of `engine_newPayload`.

The beacon chain calls one version of the method at each of its forks.

Bellatrix calls version 1, Capella version 2, Deneb version 3, and Electra and Fulu version 4.

The execution layer reads the payload at its own active fork, which that version must take.

The payload must decode into a block whose hash is the block hash of the payload.

From Deneb, its blob transactions must carry the versioned hashes of the request, in order.

The block must then pass the state transition of the execution layer on its chain.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`engine_newPayloadV1`][v1]
- [`engine_newPayloadV2`][v2]
- [`engine_newPayloadV3`][v3]
- [`engine_newPayloadV4`][v4], and its update by Amsterdam in [`amsterdam.md`][v4-amsterdam]

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_newpayloadv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_newpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_newpayloadv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#engine_newpayloadv4
[v4-amsterdam]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#update-the-methods-of-previous-forks
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Block BlockChain stateTransition)
open EthLib.Execution.Transactions (Transaction)
open EthLib.Engine.Json (AnyPayload)

variable {preset : Consensus.Preset} {fork : Fork}

/-- The version of the method that the beacon chain calls at a fork, or 0 for none.

No version here takes a payload of Gloas or later. -/
def newPayloadVersion (fork : Fork) : Nat :=
  if .glamsterdam ≤ fork then 0
  else if .pectra ≤ fork then 4
  else if .dencun ≤ fork then 3
  else if .shapella ≤ fork then 2
  else if .bellatrix ≤ fork then 1
  else 0

/-- A withdrawal of the beacon chain, as the execution layer reads it. -/
def executionWithdrawal (w : Consensus.Withdrawal) : Execution.Blocks.Withdrawal :=
  ⟨w.index, w.validatorIndex, w.address, w.amount⟩

/-- The transactions of a payload of the beacon chain, as byte arrays in order. -/
def beaconTransactions (p : Consensus.ExecutionPayload preset fork) : List ByteArray :=
  p.transactions.data.toList.map fun tx => ⟨tx.data⟩

/-- A payload of the beacon chain as the structure of the Engine API, with the fields of its fork.

It has none when the logs Bloom filter of the preset does not have 256 bytes. -/
def anyPayloadOf (p : Consensus.ExecutionPayload preset fork) : Option AnyPayload :=
  if bloom : preset.BYTES_PER_LOGS_BLOOM.toNat = 256 then
    some {
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
      withdrawals := (sinceValue p.withdrawals).map fun ws => ws.data.toList.map executionWithdrawal
      blobGasUsed := sinceValue p.blobGasUsed
      excessBlobGas := sinceValue p.excessBlobGas }
  else none

/-- The block of a payload of the beacon chain, at the active fork of a chain configuration.

The version of the method at the fork of the beacon chain must take that fork.

The payload must have exactly the fields of that fork, and so must the parameters of the method.

The block of the payload must decode, and its hash must be the block hash of the payload.

It has none when one of these fails. -/
def payloadBlock (config : ChainConfig) (p : Consensus.ExecutionPayload preset fork)
    (parentBeaconBlockRoot : Since .dencun fork Consensus.Root)
    (requests : Since .pectra fork (List ByteArray)) :
    Option ((f : Fork) × Block f Transaction) := do
  let any ← anyPayloadOf p
  let executionFork ← config.activeFork p.blockNumber.toNat p.timestamp.toNat
  if accepted : acceptsFork (newPayloadVersion fork) executionFork = true ∧
      executionFork < .glamsterdam then
    let payload ← (any.atFork executionFork).toOption
    let beacon ← (Json.since (f := .dencun) "parentBeaconBlockRoot"
      (sinceValue parentBeaconBlockRoot)).toOption
    let lists ← (Json.since (f := .pectra) "executionRequests" (sinceValue requests)).toOption
    let absent {α : Type} : Since .glamsterdam executionFork α :=
      fun h => absurd (Nat.lt_of_lt_of_le accepted.2 h) (Nat.lt_irrefl _)
    let block ← (payload.toBlock beacon lists absent absent).toOption
    return ⟨executionFork, block⟩
  else none

/-- The execution layer of the beacon chain, on a chain of the execution layer.

Each of its checks reads the block of the payload at the active fork of the chain.

The block hash is valid when that block exists.

The versioned hashes are valid when they are the hashes of its blob transactions, in order.

The payload is valid when its block passes the state transition of the chain.

The answer to a payload request is the default answer from these three checks. -/
def executionEngine (chain : BlockChain) : Consensus.ExecutionEngine preset fork where
  isValidBlockHash p root requests := (payloadBlock chain.config p root requests).isSome
  isValidVersionedHashes request :=
    match request.requestsList with
    | .ok requests =>
      match payloadBlock chain.config request.executionPayload request.parentBeaconBlockRoot
          requests with
      | some ⟨_, block⟩ =>
        (sinceValue request.versionedHashes).all fun hashes =>
          ExecutionPayload.blobVersionedHashes block.transactions == hashes.data.toList
      | none => false
    | .error _ => false
  notifyNewPayload p root requests :=
    match payloadBlock chain.config p root requests with
    | some ⟨_, block⟩ => (stateTransition chain block (checkSeal := false)).toBool
    | none => false

end EthLib.Engine
