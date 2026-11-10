module

public import EthLib.Base.ChainConfig
public import EthLib.Engine.Json
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Engine.ForkchoiceUpdated`

The choice of the head in `engine_forkchoiceUpdated`, versions 1 to 4, without a payload build.

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

The payload attributes are an object or `null`; any other value is an invalid parameter.

From version 4 the custody columns may follow, as 16 bytes or `null`.

Any other value of them is an invalid parameter.

EIP-8070 and the OpenRPC description of the method make them optional.

So version 4 also takes two parameters.

That description also makes the payload attributes optional in every version.

This model still asks for them, as `null` when there are none.

The source runs the update of the custody set apart from the forkchoice update.

So custody columns that decode never change the answer.

Payload attributes count only when the update applies a valid head.

They must then have the fields of a version of their structure that the method takes.

A field whose value is `null` counts as absent.

Otherwise the error is `-38003`, invalid payload attributes.

A field of the right name with a value of the wrong form also gives `-38003`.

Versions 2, 3 and 4 name `-38003` for a structure that the method does not take.

Version 1 names no code for that case.

This model gives it `-38003` too, the answer that step 9 of version 1 gives for invalid attributes.

Step 8 of version 1 keeps the forkchoice state applied after that error.

This model holds no state, so the error carries no head.

Versions 1, 3 and 4 of the method each take the version of the structure with their own number.

Version 2 takes versions 1 and 2 of the structure.

The fork of the attributes is the active fork at the number after the head and at their timestamp.

Each version takes some forks only, and gives `-38005` for attributes of another fork.

Version 1 takes Paris, and version 2 Paris and Shapella.

Version 3 takes the forks from Dencun on, before Glamsterdam, and version 4 takes Glamsterdam.

The update by Cancun ends version 2 at Dencun.

The update by Prague extends version 3 to Pectra, and the update by Amsterdam ends it at Glamsterdam.

So version 3 also takes Fusaka and the BPO forks, as version 4 of `engine_newPayload` does.

The source gives version 1 no rule of forks, and this model takes Paris only for it.

Version 2 takes version 1 of the structure only before Shapella, and version 2 only from it.

Otherwise the error is `-38003`.

By step 8.1 of version 1, the timestamp of the attributes must be above that of the head.

Otherwise the error is `-38003` too.

The checks run in this order: the structure, the fork, the structure at the fork, the timestamp.

Attributes that pass start a payload build.

The model returns the attributes, as those of their fork.

When the update applies no valid head, no build begins, so the attributes change nothing.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`engine_forkchoiceUpdatedV1`][v1], steps 2, 4, 5, 7, 8 and 9
- [`engine_forkchoiceUpdatedV2`][v2] and [`engine_forkchoiceUpdatedV3`][v3]
- [`engine_forkchoiceUpdatedV4`][v4], and the custody columns of [EIP-8070][eip8070]
- the updates of earlier versions by [Cancun][v2-cancun] and [Prague][v3-prague]
- the update of version 3 by [Amsterdam][v3-amsterdam]
- the [OpenRPC description][rpc] of the four versions, for the parameters that each requires

Each version has its payload attributes: [version 1][a1], [version 2][a2] and [version 3][a3].

From Glamsterdam, [version 4][a4] adds the slot number of EIP-7843 and a target gas limit.

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_forkchoiceupdatedv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_forkchoiceupdatedv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_forkchoiceupdatedv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
[v2-cancun]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#update-the-methods-of-previous-forks
[v3-prague]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#update-the-methods-of-previous-forks
[v3-amsterdam]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#update-the-methods-of-previous-forks
[eip8070]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8070.md#engine-api-extensions
[rpc]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/openrpc/methods/forkchoice.yaml
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

/-- A payload that the execution layer holds: its parent, its validity, its number and its time. -/
structure KnownPayload where
  /-- The block hash of the parent. -/
  parentHash : Hash32
  /-- Whether the payload and its ancestors are valid. -/
  valid : Bool
  /-- The number of the block. -/
  number : UInt64
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : UInt64
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

/-- The fields of version 1 of the payload attributes. -/
def attributesFieldsV1 : List String := ["timestamp", "prevRandao", "suggestedFeeRecipient"]

/-- The fields of version 2: those of version 1, and the withdrawals. -/
def attributesFieldsV2 : List String := attributesFieldsV1 ++ ["withdrawals"]

/-- The fields of version 3: those of version 2, and the root of the parent beacon block. -/
def attributesFieldsV3 : List String := attributesFieldsV2 ++ ["parentBeaconBlockRoot"]

/-- The fields of version 4: those of version 3, the slot number and the target gas limit. -/
def attributesFieldsV4 : List String := attributesFieldsV3 ++ ["slotNumber", "targetGasLimit"]

/-- The fields of a version of the payload attributes, from 1 to 4.

Version 0 reads as 1, and a version above 4 reads as 4. -/
def attributesFields : Nat → List String
  | 0 | 1 => attributesFieldsV1
  | 2 => attributesFieldsV2
  | 3 => attributesFieldsV3
  | _ => attributesFieldsV4

/-- The fork whose payload attributes have the fields of a version of their structure.

Version 1 is that of Paris, 2 of Shapella, 3 of Dencun and 4 of Glamsterdam.

Version 0 reads as 1, and a version above 4 reads as 4. -/
def attributesFork : Nat → Fork
  | 0 | 1 => .paris
  | 2 => .shapella
  | 3 => .dencun
  | _ => .glamsterdam

/-- The value of a field of an object, decoded by `f`, or none when the object lacks it. -/
def optionalField {α : Type} (fs : List (String × Json)) (name : String)
    (f : Json → Decode α) : Decode (Option α) :=
  match fs.lookup name with
  | some v => some <$> f v
  | none => pure none

/-- Payload attributes with exactly the fields of a version of their structure.

A field whose value is `null` counts as absent.

Each field holds a value of its type.

The attributes are those of the fork of that version. -/
def payloadAttributesOfJson (version : Nat) (j : Json) :
    Decode (PayloadAttributes (attributesFork version)) := do
  let fs ← fields "payloadAttributes" j
  unless hasExactly fs (attributesFields version) do invalid "payloadAttributes: wrong fields"
  let get := field "payloadAttributes" fs
  return {
    timestamp := ← uint64 "timestamp" (← get "timestamp")
    prevRandao := ← fixed "prevRandao" 32 (← get "prevRandao")
    suggestedFeeRecipient := ← address "suggestedFeeRecipient" (← get "suggestedFeeRecipient")
    withdrawals := ← since "withdrawals"
      (← optionalField fs "withdrawals" (array "withdrawals" withdrawal))
    parentBeaconBlockRoot := ← since "parentBeaconBlockRoot"
      (← optionalField fs "parentBeaconBlockRoot" (fixed "parentBeaconBlockRoot" 32))
    slotNumber := ← since "slotNumber" (← optionalField fs "slotNumber" (uint64 "slotNumber"))
    targetGasLimit := ← since "targetGasLimit"
      (← optionalField fs "targetGasLimit" (uint64 "targetGasLimit")) }

/-- The versions of the structure of the payload attributes that a version of the method takes.

Version 2 takes versions 1 and 2, and the fork of the timestamp then picks one of them.

Any other version takes its own number. -/
def attributesVersions : Nat → List Nat
  | 2 => [1, 2]
  | version => [version]

/-- The payload attributes that a version of the method takes, with the fork of their structure.

The first structure that fits gives them.

Attributes that fit no structure that the method takes are invalid payload attributes. -/
def payloadAttributesOfVersion (version : Nat) (j : Json) :
    Except EngineError (Σ fork, PayloadAttributes fork) :=
  match (attributesVersions version).findSome?
      (fun v => (payloadAttributesOfJson v j).toOption.map fun a => ⟨attributesFork v, a⟩) with
  | some attributes => .ok attributes
  | none => .error .invalidPayloadAttributes

/-- The custody columns of version 4: 16 bytes, one bit for each column.

They are `null` when the consensus layer gives no custody set. -/
def custodyColumnsOfJson : Json → Decode (Option (Vector UInt8 16))
  | .null => pure none
  | j => some <$> fixed "custodyColumns" 16 j

/-- The parameters of a version of the method.

They are the forkchoice state, then the payload attributes, an object or `null`.

From version 4 the custody columns may follow, as 16 bytes or `null`.

The source checks the fields of the attributes only when a valid head is applied.

The result is the state, and the attributes when they are an object. -/
def forkchoiceUpdatedParams (version : Nat) (params : Json) :
    Decode (ForkchoiceState × Option Json) := do
  let params ← paramsArray params
  let (state, attributes, custody) ← match params, decide (4 ≤ version) with
    | [state, attributes], _ => pure (state, attributes, Json.null)
    | [state, attributes, custody], true => pure (state, attributes, custody)
    | _, four => invalid s!"params: got {params.length}, expected {if four then "2 or 3" else "2"}"
  let state ← forkchoiceStateOfJson state
  let attributes ← match attributes with
    | .null => pure none
    | .obj kvs => pure (some (Json.obj kvs))
    | _ => invalid "payloadAttributes: not an object"
  -- The custody set changes the blob pool only, never the answer, so its value is dropped.
  let _ ← custodyColumnsOfJson custody
  return (state, attributes)

/-- Whether a version of the method takes payload attributes whose timestamp is in a fork.

Version 1 takes Paris, and version 2 Paris and Shapella.

Version 3 takes the forks from Dencun up to Glamsterdam, which it does not take.

Version 4 takes Glamsterdam.

Version 0 reads as 1, and a version above 4 reads as 4. -/
def attributesTakeFork : Nat → Fork → Bool
  | 0, fork | 1, fork => fork == .paris
  | 2, fork => fork == .paris || fork == .shapella
  | 3, fork => decide (.dencun ≤ fork) && decide (fork < .glamsterdam)
  | _, fork => fork == .glamsterdam

/-- The fork of the structure of the payload attributes whose timestamp is in a fork.

Before Shapella it is Paris, then Shapella before Dencun, then Dencun before Glamsterdam.

From Glamsterdam it is Glamsterdam. -/
def attributesForkAt (fork : Fork) : Fork :=
  if fork < .shapella then .paris
  else if fork < .dencun then .shapella
  else if fork < .glamsterdam then .dencun
  else .glamsterdam

/-- The fork of the structure has the withdrawals exactly when the fork has them. -/
theorem shapella_le_attributesForkAt_iff (fork : Fork) :
    .shapella ≤ attributesForkAt fork ↔ .shapella ≤ fork := by
  cases fork <;> decide

/-- The fork of the structure has the parent beacon block root exactly when the fork has it. -/
theorem dencun_le_attributesForkAt_iff (fork : Fork) :
    .dencun ≤ attributesForkAt fork ↔ .dencun ≤ fork := by
  cases fork <;> decide

/-- The fork of the structure has the slot number exactly when the fork has it. -/
theorem glamsterdam_le_attributesForkAt_iff (fork : Fork) :
    .glamsterdam ≤ attributesForkAt fork ↔ .glamsterdam ≤ fork := by
  cases fork <;> decide

/-- Payload attributes of the structure of a fork, as attributes of that fork, field by field. -/
def PayloadAttributes.ofStructure {fork : Fork} (a : PayloadAttributes (attributesForkAt fork)) :
    PayloadAttributes fork where
  timestamp := a.timestamp
  prevRandao := a.prevRandao
  suggestedFeeRecipient := a.suggestedFeeRecipient
  withdrawals h := a.withdrawals ((shapella_le_attributesForkAt_iff fork).mpr h)
  parentBeaconBlockRoot h := a.parentBeaconBlockRoot ((dencun_le_attributesForkAt_iff fork).mpr h)
  slotNumber h := a.slotNumber ((glamsterdam_le_attributesForkAt_iff fork).mpr h)
  targetGasLimit h := a.targetGasLimit ((glamsterdam_le_attributesForkAt_iff fork).mpr h)

/-- Payload attributes at a fork, when their structure is that of the fork.

Otherwise there are none. -/
def PayloadAttributes.toFork (a : Σ f, PayloadAttributes f) (fork : Fork) :
    Option (PayloadAttributes fork) :=
  if h : attributesForkAt fork = a.1 then some (PayloadAttributes.ofStructure (h ▸ a.2)) else none

/-- The checks of decoded payload attributes against the head that they build on.

The fork of the attributes is the active fork at the number after the head and at their timestamp.

A version of the method that does not take that fork gives `-38005`, as do attributes of no fork.

Attributes whose structure is not that of the fork give `-38003`.

Only version 2 can fail that way, since each other version takes a single structure.

Attributes whose timestamp is not above that of the head give `-38003` too.

The result is the attributes at their fork. -/
def checkAttributes (config : ChainConfig) (version : Nat) (head : KnownPayload)
    (attributes : Σ f, PayloadAttributes f) :
    Except EngineError (Σ fork, PayloadAttributes fork) := do
  let timestamp := attributes.2.timestamp
  let some fork := config.activeFork (head.number.toNat + 1) timestamp.toNat
    | throw .unsupportedFork
  unless attributesTakeFork version fork do throw .unsupportedFork
  let some atFork := PayloadAttributes.toFork attributes fork | throw .invalidPayloadAttributes
  unless head.timestamp < timestamp do throw .invalidPayloadAttributes
  return ⟨fork, atFork⟩

/-- A version of the method: its status, the new head, and the payload attributes of a build.

Attributes count only when a valid head is applied.

They must then fit a structure of the version, and then pass the checks against the head.

The attributes of a build are those of the fork of their timestamp.

The versions of the method are 1 to 4; the C export passes no other.

Version 0 reads as 1, and a version above 4 reads as 4. -/
def forkchoiceUpdatedCall (config : ChainConfig) (version : Nat) (tree : PayloadTree)
    (finalized : Option Hash32) (params : Json) :
    Except EngineError
      (PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)) := do
  let (state, attributes) ← forkchoiceUpdatedParams version params
  let (status, head) ← forkchoiceUpdated tree finalized state
  match attributes, head with
  | some j, some h =>
    let decoded ← payloadAttributesOfVersion version j
    -- The update applies only a head that the tree holds.
    let some known := tree.lookup h | return (status, head, none)
    return (status, head, some (← checkAttributes config version known decoded))
  | _, _ => return (status, head, none)

end EthLib.Engine
