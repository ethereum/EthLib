module

public import EthLib.Engine.Json
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Engine.ForkchoiceUpdated`

The choice of the head in `engine_forkchoiceUpdated`, versions 1 to 3, without a payload build.

The consensus layer names a head, a safe block and a finalized block.

The execution layer knows a tree of payloads, each with its parent and its validity.

A head that the tree does not hold is syncing.

A head that is invalid stays invalid, with the latest valid ancestor as the latest valid hash.

The execution layer may also know a finalized block, the latest one that an earlier update named.

A valid head below that block is valid, and the forkchoice state is neither checked nor applied.

The source allows the update to be skipped there, and this model skips it.

A head equal to that block follows the steps below, as for any other valid head.

A valid head becomes the head of the canonical chain.

The safe and the finalized block must then be the head or its ancestors, unless they are zero.

The source allows zero hashes only until the transition block is finalized.

This model has no transition block, so it accepts zero hashes at any time.

Otherwise the state is invalid, with JSON-RPC code `-38002`.

The parameters are the forkchoice state, with exactly its three fields, and the payload attributes.

Payload attributes start a payload build only when the update selects a new valid head.

That build is not specified here, so such a request is refused.

With any other answer no build begins, so the payload attributes change nothing.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`engine_forkchoiceUpdatedV1`][v1], steps 2, 4, 5, 7, 8 and 9
- [`engine_forkchoiceUpdatedV2`][v2] and [`engine_forkchoiceUpdatedV3`][v3]

Each version has its payload attributes: [version 1][a1], [version 2][a2] and [version 3][a3].

From Glamsterdam, [version 4][a4] adds the slot number of EIP-7843 and a target gas limit.

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_forkchoiceupdatedv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_forkchoiceupdatedv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_forkchoiceupdatedv3
[a1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payloadattributesv1
[a2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#payloadattributesv2
[a3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#payloadattributesv3
[a4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#payloadattributesv4
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Engine.Json
open Lean (Json)

/-- The attributes of a payload that the consensus layer asks the execution layer to build. -/
structure PayloadAttributes (fork : Fork) : Type where
  /-- The timestamp of the payload. -/
  timestamp : UInt64
  /-- The RANDAO mix of the payload. -/
  prevRandao : Bytes32
  /-- The fee recipient that the consensus layer suggests; the builder may choose another. -/
  suggestedFeeRecipient : Address
  /-- The withdrawals of the payload, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)
  /-- The root of the parent beacon block, from Dencun. -/
  parentBeaconBlockRoot : Since .dencun fork Hash32
  /-- The slot of the payload, from Glamsterdam. -/
  slotNumber : Since .glamsterdam fork UInt64
  /-- The target of the gas limit of the payload, from Glamsterdam. -/
  targetGasLimit : Since .glamsterdam fork UInt64

/-- A payload that the execution layer holds: its parent and whether it is valid. -/
structure KnownPayload where
  /-- The block hash of the parent. -/
  parentHash : Hash32
  /-- Whether the payload and its ancestors are valid. -/
  valid : Bool
  deriving DecidableEq, Repr

/-- The payloads that the execution layer holds, by block hash. -/
abbrev PayloadTree := List (Hash32 × KnownPayload)

/-- The hash of thirty-two zero bytes, which stands for no block. -/
def ZERO_HASH : Hash32 := Vector.replicate 32 0

/-- The hashes from a block back through its known ancestors, at most `fuel` of them. -/
def ancestors (tree : PayloadTree) : Nat → Hash32 → List Hash32
  | 0, _ => []
  | fuel + 1, hash =>
    match tree.lookup hash with
    | some p => hash :: ancestors tree fuel p.parentHash
    | none => []

/-- The chain of a block in a tree: the block and its known ancestors. -/
def chainOf (tree : PayloadTree) (hash : Hash32) : List Hash32 :=
  ancestors tree tree.length hash

/-- The most recent valid block on the chain of a block, if any. -/
def latestValid (tree : PayloadTree) (hash : Hash32) : Option Hash32 :=
  (chainOf tree hash).find? fun h => (tree.lookup h).any (·.valid)

/-- Whether a block of the forkchoice state is zero or on the chain of the head. -/
def onChain (tree : PayloadTree) (head hash : Hash32) : Bool :=
  hash == ZERO_HASH || (chainOf tree head).contains hash

/-- Whether a block is a strict ancestor of the finalized block that the execution layer knows.

It is not when the execution layer knows no finalized block. -/
def belowFinalized (tree : PayloadTree) (finalized : Option Hash32) (hash : Hash32) : Bool :=
  match finalized with
  | some f => hash != f && (chainOf tree f).contains hash
  | none => false

/-- The status of a forkchoice update, and the new head when it changes.

The execution layer knows the payloads of the tree, and the finalized block of an earlier update.
-/
def forkchoiceUpdated (tree : PayloadTree) (finalized : Option Hash32) (state : ForkchoiceState) :
    Except EngineError (PayloadStatus × Option Hash32) :=
  match tree.lookup state.headBlockHash with
  | none => pure (⟨.syncing, none⟩, none)
  | some head =>
    if !head.valid then pure (⟨.invalid, latestValid tree state.headBlockHash⟩, none)
    -- Step 2: a valid head below the known finalized block is valid, and the update is skipped.
    else if belowFinalized tree finalized state.headBlockHash then
      pure (⟨.valid, some state.headBlockHash⟩, none)
    else if onChain tree state.headBlockHash state.safeBlockHash &&
        onChain tree state.headBlockHash state.finalizedBlockHash then
      pure (⟨.valid, some state.headBlockHash⟩, some state.headBlockHash)
    else throw .invalidForkchoiceState

/-- The forkchoice state, with exactly its three fields. -/
def forkchoiceStateOfJson (j : Json) : Decode ForkchoiceState := do
  let fs ← fields "forkchoiceState" j
  unless hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] do
    invalid "forkchoiceState: wrong fields"
  let get := field "forkchoiceState" fs
  return {
    headBlockHash := ← fixed "headBlockHash" 32 (← get "headBlockHash")
    safeBlockHash := ← fixed "safeBlockHash" 32 (← get "safeBlockHash")
    finalizedBlockHash := ← fixed "finalizedBlockHash" 32 (← get "finalizedBlockHash") }

/-- The parameters of a version of the method: the forkchoice state, then the payload attributes.

It returns the state, and whether the attributes are not `null`. -/
def forkchoiceUpdatedParams (params : Json) : Decode (ForkchoiceState × Bool) := do
  let .arr items := params | invalid "params: not an array"
  let [state, attributes] := items.toList | invalid "params: not 2 values"
  let state ← forkchoiceStateOfJson state
  return (state, !attributes.isNull)

end EthLib.Engine
