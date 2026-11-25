module

public import EthLib.Base.ByteOrder
public import EthLib.Base.ChainConfig
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Engine.Json
public import EthLib.Engine.TransitionConfiguration
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Engine.ForkchoiceUpdated`

The choice of the head in `engine_forkchoiceUpdated`, versions 1 to 5, without a payload build.

Sources, at commit `1ca0818` of execution-apis:

- versions [1][v1], [2][v2], [3][v3], [4][v4] and [5][v5], and their [OpenRPC description][rpc]
- the updates of earlier versions by [Cancun][v2-cancun], [Prague][v3-prague] and [Osaka][osaka]
- the updates of version 3 by [Amsterdam][v3-amsterdam] and of version 4 by [Bogota][v4-bogota]

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_forkchoiceupdatedv1
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#engine_forkchoiceupdatedv2
[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#engine_forkchoiceupdatedv3
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
[v2-cancun]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#update-the-methods-of-previous-forks
[v3-prague]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/prague.md#update-the-methods-of-previous-forks
[osaka]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#update-the-methods-of-previous-forks
[v3-amsterdam]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#update-the-methods-of-previous-forks
[rpc]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/openrpc/methods/forkchoice.yaml
[v5]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#engine_forkchoiceupdatedv5
[v4-bogota]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#update-the-methods-of-previous-forks
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Rpc (withdrawal withdrawalJson)
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
  /-- The slot of the payload, from Glamsterdam, by EIP-7843. -/
  slotNumber : Since .glamsterdam fork UInt64
  /-- The target of the gas limit of the payload, from Glamsterdam. -/
  targetGasLimit : Since .glamsterdam fork UInt64
  /-- The transactions of the inclusion lists that the payload must satisfy, from Hegotá.

  They come from EIP-7805.

  Each is any byte string, and one that does not decode as a transaction is still taken. -/
  inclusionListTransactions : Since .hegota fork (List ByteArray)

/-- A block that the execution layer holds: its parent, its validity, its number and its time.

It is a payload, or a block of proof of work with its total difficulty and that of its parent. -/
structure KnownPayload where
  /-- The block hash of the parent. -/
  parentHash : Hash32
  /-- Whether the block and its ancestors are valid. -/
  valid : Bool
  /-- The number of the block, unbounded as in its header. -/
  number : Nat
  /-- The time of the block, in seconds since the Unix epoch, unbounded as in its header. -/
  timestamp : Nat
  /-- For a block of proof of work, its total difficulty and its parent's; `none` otherwise. -/
  powTotalDifficulty : Option (Nat × Nat)
  deriving DecidableEq, Repr

/-- Whether a known block is a block of proof of work. -/
def KnownPayload.isPow (p : KnownPayload) : Bool := p.powTotalDifficulty.isSome

/-- The payloads that the execution layer holds, by block hash. -/
abbrev PayloadTree := List (Hash32 × KnownPayload)

/-- The hashes from a block back through its known ancestors, at most `fuel` of them. -/
def ancestors (tree : PayloadTree) : Nat → Hash32 → List Hash32
  -- The fuel bounds the walk, so a tree whose parents form a cycle still ends.
  | 0, _ => []
  | fuel + 1, hash =>
    match tree.lookup hash with
    -- A held block, then the ancestors of its parent.
    | some p => hash :: ancestors tree fuel p.parentHash
    -- The chain stops at the first block that the tree does not hold.
    | none => []

/-- The chain of a block in a tree: the block and its known ancestors. -/
def chainOf (tree : PayloadTree) (hash : Hash32) : List Hash32 :=
  -- A chain without a cycle holds each block of the tree at most once, so this fuel suffices.
  ancestors tree tree.length hash

/-- The most recent valid block on the chain of a block, if any. -/
def latestValid (tree : PayloadTree) (hash : Hash32) : Option Hash32 :=
  -- Payload validation, step 3: the ancestor that is `VALID`, below ancestors that are `INVALID`.
  --
  -- The chain runs from the block down, so its first valid block is that ancestor.
  (chainOf tree hash).find? fun h => (tree.lookup h).any (·.valid)

/-- The latest valid hash of an invalid block: the latest valid block of its chain.

It follows step 3 of the [payload validation][validation] of Paris.

[validation]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payload-validation
-/
def latestValidHash (tree : PayloadTree) (hash : Hash32) : Option Hash32 :=
  -- Payload validation, step 3: the latest valid hash is the block hash of that ancestor.
  --
  -- It is `0x00..00` when that ancestor is a PoW block.
  --
  -- It is `null` when no such ancestor is known.
  (latestValid tree hash).map fun v => if (tree.lookup v).any (·.isPow) then ZERO_HASH else v

/-- The totals of the most recent block of proof of work on the chain of a block, if any. -/
def latestPow (tree : PayloadTree) (hash : Hash32) : Option (Nat × Nat) :=
  -- A step without a version is a step of version 1 of the method.
  --
  -- Payload validation, step 2, reads the most recent PoW block among the ancestors of a payload.
  --
  -- Step 3 reads the head when it is a PoW block, so the block itself counts here.
  (chainOf tree hash).findSome? fun h => (tree.lookup h).bind (·.powTotalDifficulty)

/-- Whether the chain of a block passes the terminal block check.

It reads the [definitions][eip3675] of EIP-3675, for a terminal block of proof of work.

[eip3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/
def chainPassesTerminalCheck (transition : TransitionConfiguration) (tree : PayloadTree)
    (hash : Hash32) : Bool :=
  match latestPow tree hash with
  -- EIP-3675: a terminal PoW block has a total difficulty of at least the terminal one.
  --
  -- Its parent has a total difficulty below the terminal one.
  | some (totalDifficulty, parentTotalDifficulty) =>
    isTerminalPowBlock transition totalDifficulty parentTotalDifficulty
  -- No PoW block in the tree: EthLib takes the chain as one after the transition, so it passes.
  | none => true

/-- Whether the transition block is finalized: the known finalized block is a payload in the tree.

The finalized hash of the request does not count. -/
def transitionFinalized (tree : PayloadTree) (finalized : Option Hash32) : Bool :=
  match finalized.bind (tree.lookup ·) with
  -- EIP-3675: `TRANSITION_BLOCK` is the earliest PoS block of the canonical chain.
  --
  -- A finalized PoS block is that block or a descendant of it, so that block is finalized too.
  | some p => !p.isPow
  -- Without a known finalized block, or with one that the tree does not hold, EthLib says no.
  | none => false

/-- Whether the forkchoice state has a zero safe or finalized hash after the transition. -/
def zeroAfterTransition (tree : PayloadTree) (finalized : Option Hash32)
    (state : ForkchoiceState) : Bool :=
  -- The note on zero hashes of `ForkchoiceStateV1`, once the transition block is finalized.
  transitionFinalized tree finalized &&
    (state.safeBlockHash == ZERO_HASH || state.finalizedBlockHash == ZERO_HASH)

/-- Whether a block of the forkchoice state is zero or on the chain of the head. -/
def onChain (tree : PayloadTree) (head hash : Hash32) : Bool :=
  -- A zero hash passes here, and the check of zero hashes after the transition runs apart.
  --
  -- Otherwise the block is the head or one of the ancestors of the head that the tree holds.
  hash == ZERO_HASH || (chainOf tree head).contains hash

/-- Whether a block is a strict ancestor of the finalized block that the execution layer knows. -/
def belowFinalized (tree : PayloadTree) (finalized : Option Hash32) (hash : Hash32) : Bool :=
  match finalized with
  -- Step 2: an ancestor of the latest known finalized block.
  --
  -- EthLib reads ancestor as strict, so a head equal to that block runs the steps after step 2.
  | some f => hash != f && (chainOf tree f).contains hash
  -- Step 2 needs a known finalized block.
  | none => false

/-- The status of a forkchoice update, and the new head when it changes. -/
def forkchoiceUpdated (transition : TransitionConfiguration) (tree : PayloadTree)
    (finalized : Option Hash32) (state : ForkchoiceState) :
    Except EngineError (PayloadStatus × Option Hash32) :=
  -- The consensus layer names a head, a safe block and a finalized block.
  --
  -- The execution layer knows the blocks of the tree, and the finalized block of an earlier update.
  --
  -- Its configuration of the transition gives the terminal total difficulty.
  match tree.lookup state.headBlockHash with
  -- Steps 1 and 9: an unknown head is `SYNCING`, with a `null` latest valid hash.
  --
  -- Step 1 lets the client start a sync, which EthLib leaves out.
  | none => pure (⟨.syncing, none⟩, none)
  | some head =>
    -- Step 3: a PoW head satisfies the terminal block conditions of EIP-3675.
    --
    -- Payload validation, step 2: so does the most recent PoW block among the ancestors.
    --
    -- On failure, step 9 answers `INVALID` with `0x00..00`, and the state is not updated.
    --
    -- Version 2, step 1 lets a client skip both checks.
    --
    -- EthLib runs them in every version, so that one rule serves all versions.
    --
    -- The check runs first, since a chain that fails it is not `VALID`, as step 2 below needs.
    if !chainPassesTerminalCheck transition tree state.headBlockHash then
      pure (⟨.invalid, some ZERO_HASH⟩, none)
    -- Step 4: the head must be `VALID`, or the state is not updated.
    --
    -- Step 9: an `INVALID` head has the `validHash` of payload validation, step 3.
    --
    -- The tree holds the result of payload validation, which EthLib does not run.
    else if !head.valid then pure (⟨.invalid, latestValidHash tree state.headBlockHash⟩, none)
    -- Step 2: a `VALID` ancestor of the known finalized block is `VALID`, with its own hash.
    --
    -- The client may skip the update, and EthLib skips it, so the checks of the state do not run.
    --
    -- No payload build begins, since no head is applied.
    else if belowFinalized tree finalized state.headBlockHash then
      pure (⟨.valid, some state.headBlockHash⟩, none)
    -- `ForkchoiceStateV1`, note: the safe and the finalized hash may be `0x00..00`.
    --
    -- They may be so unless the transition block is finalized.
    --
    -- No step names an error for that case, and EthLib gives the `-38002` of step 9.
    --
    -- Step 9 gives `-38002` to a state that is invalid or inconsistent.
    else if zeroAfterTransition tree finalized state then
      throw (.invalidForkchoiceState state.safeBlockHash state.finalizedBlockHash)
    -- Step 5: the safe and the finalized block belong to the chain of the `VALID` head.
    else if onChain tree state.headBlockHash state.safeBlockHash &&
        onChain tree state.headBlockHash state.finalizedBlockHash then
      -- Step 7: the head is `VALID`, and so is a nonzero finalized block, as its ancestor.
      --
      -- So the state is updated to the head.
      --
      -- A zero finalized hash names no payload, and EthLib updates the state then too.
      --
      -- The note of `ForkchoiceStateV1` allows that hash until the transition block is finalized.
      --
      -- Step 9: `VALID`, with the hash of the head as the latest valid hash.
      --
      -- Step 6 is left out, since the source lets each client set the deepest reorg it takes.
      --
      -- Past that depth, step 6 returns `-38006`.
      pure (⟨.valid, some state.headBlockHash⟩, some state.headBlockHash)
    -- Step 5: otherwise `-38002`, invalid forkchoice state.
    else throw (.invalidForkchoiceState state.safeBlockHash state.finalizedBlockHash)

/-- The forkchoice state, with exactly its three fields.

Its structure is [`ForkchoiceStateV1`][fcs].

Its note allows zero safe and finalized hashes until the transition block is finalized.

[fcs]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#forkchoicestatev1
-/
def forkchoiceStateOfJson (j : Json) : Decode ForkchoiceState := do
  -- Version 3, step 1: the state matches `ForkchoiceStateV1`, or `-32602`.
  --
  -- Versions 1 and 2 state no such step, and EthLib checks them the same way.
  --
  -- A field whose value is `null` counts as absent, so it fails the match.
  let fs ← fields "forkchoiceState" j
  unless hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] do
    invalid "forkchoiceState: wrong fields"
  let get := field "forkchoiceState" fs
  -- `ForkchoiceStateV1`: each of the three hashes is `DATA` of 32 bytes.
  return {
    headBlockHash := ← fixed "headBlockHash" 32 (← get "headBlockHash")
    safeBlockHash := ← fixed "safeBlockHash" 32 (← get "safeBlockHash")
    finalizedBlockHash := ← fixed "finalizedBlockHash" 32 (← get "finalizedBlockHash") }

/-- The forkchoice state as JSON, with its three hashes. -/
def forkchoiceStateJson (state : ForkchoiceState) : Json :=
  -- `ForkchoiceStateV1`: the three hashes, each as `DATA` of 32 bytes.
  Json.mkObj [("headBlockHash", dataJson state.headBlockHash.toList),
    ("safeBlockHash", dataJson state.safeBlockHash.toList),
    ("finalizedBlockHash", dataJson state.finalizedBlockHash.toList)]

/-- The fields of [version 1][a1] of the payload attributes.

[a1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payloadattributesv1
-/
def attributesFieldsV1 : List String := ["timestamp", "prevRandao", "suggestedFeeRecipient"]

/-- The fields of [version 2][a2]: those of version 1, and the withdrawals.

[a2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#payloadattributesv2
-/
def attributesFieldsV2 : List String := attributesFieldsV1 ++ ["withdrawals"]

/-- The fields of [version 3][a3]: those of version 2, and the root of the parent beacon block.

[a3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#payloadattributesv3
-/
def attributesFieldsV3 : List String := attributesFieldsV2 ++ ["parentBeaconBlockRoot"]

/-- The fields of [version 4][a4]: those of version 3, the slot number and the target gas limit.

[a4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#payloadattributesv4
-/
def attributesFieldsV4 : List String := attributesFieldsV3 ++ ["slotNumber", "targetGasLimit"]

/-- The fields of [version 5][a5]: those of version 4, and the inclusion list transactions.

[a5]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#payloadattributesv5
-/
def attributesFieldsV5 : List String := attributesFieldsV4 ++ ["inclusionListTransactions"]

/-- The fields of a version of the payload attributes, from 1 to 5.

Version 0 reads as 1, and a version above 5 reads as 5. -/
def attributesFields : Nat → List String
  | 0 | 1 => attributesFieldsV1
  | 2 => attributesFieldsV2
  | 3 => attributesFieldsV3
  | 4 => attributesFieldsV4
  | _ => attributesFieldsV5

/-- The fork whose payload attributes have the fields of a version of their structure.

Version 0 reads as 1, and a version above 5 reads as 5. -/
def attributesFork : Nat → Fork
  -- Version 1 is that of Paris, 2 of Shapella, 3 of Dencun, 4 of Glamsterdam and 5 of Hegotá.
  | 0 | 1 => .paris
  | 2 => .shapella
  | 3 => .dencun
  | 4 => .glamsterdam
  | _ => .hegota

/-- The value of a field of an object, decoded by `f`, or none when the object lacks it. -/
def optionalField {α : Type} (fs : List (String × Json)) (name : String)
    (f : Json → Read α) : Read (Option α) :=
  match fs.lookup name with
  | some v => some <$> f v
  | none => pure none

/-- Payload attributes with exactly the fields of a version of their structure.

The attributes are those of the fork of that version. -/
def payloadAttributesOfJson (version : Nat) (j : Json) :
    Decode (PayloadAttributes (attributesFork version)) := do
  -- A field whose value is `null` counts as absent.
  let fs ← fields "payloadAttributes" j
  -- The attributes match the structure of the version: each of its fields, and no other.
  unless hasExactly fs (attributesFields version) do invalid "payloadAttributes: wrong fields"
  let get := field "payloadAttributes" fs
  -- Each field holds a value of the type that the structure gives it.
  return {
    -- `PayloadAttributesV1`: `timestamp` is a `QUANTITY` of 64 bits.
    timestamp := ← uint64 "timestamp" (← get "timestamp")
    -- `PayloadAttributesV1`: `prevRandao` is `DATA` of 32 bytes.
    prevRandao := ← fixed "prevRandao" 32 (← get "prevRandao")
    -- `PayloadAttributesV1`: `suggestedFeeRecipient` is `DATA` of 20 bytes.
    suggestedFeeRecipient := ← address "suggestedFeeRecipient" (← get "suggestedFeeRecipient")
    -- `PayloadAttributesV2` adds `withdrawals`, an array of `WithdrawalV1`.
    withdrawals := ← since "withdrawals"
      (← optionalField fs "withdrawals" (array "withdrawals" withdrawal))
    -- `PayloadAttributesV3` adds `parentBeaconBlockRoot`, `DATA` of 32 bytes.
    parentBeaconBlockRoot := ← since "parentBeaconBlockRoot"
      (← optionalField fs "parentBeaconBlockRoot" (fixed "parentBeaconBlockRoot" 32))
    -- `PayloadAttributesV4` adds `slotNumber` and `targetGasLimit`, each a `QUANTITY` of 64 bits.
    slotNumber := ← since "slotNumber" (← optionalField fs "slotNumber" (uint64 "slotNumber"))
    targetGasLimit := ← since "targetGasLimit"
      (← optionalField fs "targetGasLimit" (uint64 "targetGasLimit"))
    -- `PayloadAttributesV5` adds `inclusionListTransactions`, an array of `DATA`.
    --
    -- Each entry is any byte string, and one that does not decode as a transaction still reads.
    inclusionListTransactions := ← since "inclusionListTransactions"
      (← optionalField fs "inclusionListTransactions" inclusionListOfJson) }

/-- Payload attributes as JSON, with the fields of their fork's structure, versions 1 to 5. -/
def payloadAttributesJson {fork : Fork} (a : PayloadAttributes fork) : Json :=
  -- `PayloadAttributesV1`: the timestamp as a `QUANTITY`, the RANDAO mix and the fee recipient.
  Json.mkObj ([("timestamp", quantityJson a.timestamp.toNat),
      ("prevRandao", dataJson a.prevRandao.toList),
      ("suggestedFeeRecipient", dataJson a.suggestedFeeRecipient.toList)] ++
    -- `PayloadAttributesV2`, from Shapella: the withdrawals.
    (if h : .shapella ≤ fork then [("withdrawals", listJson withdrawalJson (a.withdrawals h))]
      else []) ++
    -- `PayloadAttributesV3`, from Dencun: the root of the parent beacon block.
    (if h : .dencun ≤ fork then
      [("parentBeaconBlockRoot", dataJson (a.parentBeaconBlockRoot h).toList)] else []) ++
    -- `PayloadAttributesV4`, from Glamsterdam: the slot number and the target gas limit.
    (if h : .glamsterdam ≤ fork then
      [("slotNumber", quantityJson (a.slotNumber h).toNat),
        ("targetGasLimit", quantityJson (a.targetGasLimit h).toNat)] else []) ++
    -- `PayloadAttributesV5`, from Hegotá: the transactions of the inclusion lists.
    (if h : .hegota ≤ fork then
      [("inclusionListTransactions", inclusionListJson (a.inclusionListTransactions h))]
      else []))

/-- The versions of the structure of the payload attributes that a version of the method takes. -/
def attributesVersions : Nat → List Nat
  -- Version 2, parameter 2: `PayloadAttributesV1` or `PayloadAttributesV2`.
  --
  -- The fork of the timestamp then picks one of them.
  | 2 => [1, 2]
  -- Versions 1, 3, 4 and 5, parameter 2: the structure with their own number.
  | version => [version]

/-- The payload attributes that a version of the method takes, with the fork of their structure.

The first structure that fits gives them. -/
def payloadAttributesOfVersion (version : Nat) (j : Json) :
    Except EngineError (Σ fork, PayloadAttributes fork) :=
  -- Version 3, step 2.1, and versions 4 and 5, step 1.1: the attributes match the structure.
  match (attributesVersions version).findSome?
      (fun v => (payloadAttributesOfJson v j).toOption.map fun a => ⟨attributesFork v, a⟩) with
  | some attributes => .ok attributes
  -- Otherwise `-38003`, and a field of the right name with a value of the wrong form fails too.
  --
  -- Version 2 names `-38003` for the wrong version of the structure.
  --
  -- Version 1 names no code, and EthLib gives the `-38003` of step 9 for invalid attributes.
  | none => .error .invalidPayloadAttributes

/-- The custody columns of version 4: 16 bytes, one bit for each column.

They come from [EIP-8070][eip8070].

[eip8070]: https://github.com/ethereum/EIPs/blob/b055feec322fbc37e9d77a393a50b3ff56b31c92/EIPS/eip-8070.md#engine-api-extensions
-/
def custodyColumnsOfJson : Json → Decode (Option (Vector UInt8 16))
  -- Version 4, parameter 3: `null` when the consensus layer gives no custody set.
  | .null => pure none
  -- Version 4, step 3.1: a value other than `null` is `DATA` of 16 bytes, or `-32602`.
  | j => some <$> fixed "custodyColumns" 16 j

/-- The parameters of a version of the method.

The result is the state, and the attributes when they are an object. -/
def forkchoiceUpdatedParams (version : Nat) (params : Json) :
    Decode (ForkchoiceState × Option Json) := do
  let params ← paramsArray params
  -- The forkchoice state and the payload attributes, then from version 4 the custody columns.
  let (state, attributes, custody) ← match params, decide (4 ≤ version) with
    -- The OpenRPC description makes the attributes optional in every version.
    --
    -- A request without them reads as one with `null`.
    | [state], _ => pure (state, Json.null, Json.null)
    | [state, attributes], _ => pure (state, attributes, Json.null)
    -- Version 4, parameter 3: the custody columns, which the OpenRPC description makes optional.
    --
    -- EIP-8070 makes them optional too, so versions 4 and 5 take one to three parameters.
    | [state, attributes, custody], true => pure (state, attributes, custody)
    -- Any other count of parameters is `-32602`.
    | _, four => invalid s!"params: got {params.length}, expected {if four then "1 to 3" else "1 or 2"}"
  -- Parameter 1: `ForkchoiceStateV1`.
  let state ← forkchoiceStateOfJson state
  -- Parameter 2: `Object|null`, and EthLib gives `-32602` to any other value.
  --
  -- Step 8 checks the fields of the attributes only once a valid head is applied.
  let attributes ← match attributes with
    | .null => pure none
    | .obj kvs => pure (some (Json.obj kvs))
    | _ => invalid "payloadAttributes: not an object"
  -- Version 4, step 3.4: the custody set updates apart from the forkchoice update.
  --
  -- It changes the blob pool only, so columns that decode never change the answer.
  let _ ← custodyColumnsOfJson custody
  return (state, attributes)

/-- The parameters of a version of the method as JSON.

The attributes have the structure of their fork, which the version must take. -/
def forkchoiceUpdatedParamsJson {fork : Fork} (version : Nat) (state : ForkchoiceState)
    (attributes : Option (PayloadAttributes fork)) (custody : Option (Vector UInt8 16)) : Json :=
  -- The consensus layer writes the forkchoice state, the attributes and the parameters as JSON.
  --
  -- Parameters 1 and 2: the forkchoice state, then the payload attributes or `null`.
  .arr ([forkchoiceStateJson state, optionJson payloadAttributesJson attributes] ++
    -- Parameter 3, from version 4: the custody columns as 16 bytes or `null`; before, none.
    if 4 ≤ version then [optionJson (dataJson ·.toList) custody] else []).toArray

/-- Whether a version of the method takes payload attributes whose timestamp is in a fork.

Version 0 reads as 1, and a version above 5 reads as 5. -/
def attributesTakeFork : Nat → Fork → Bool
  -- Version 1 states no rule of forks, and version 2, step 2 sends Shapella to version 2.
  --
  -- So EthLib takes Paris only, as version 1 of the method that checks a payload does.
  | 0, fork | 1, fork => fork == .paris
  -- Version 2: Paris and Shapella, since the update by Cancun gives `-38005` from Dencun on.
  | 2, fork => fork == .paris || fork == .shapella
  -- Version 3, step 2.2: Cancun, here Dencun, and the update by Prague adds Prague, here Pectra.
  --
  -- The update by Osaka adds Osaka, here Fusaka.
  --
  -- The update by Amsterdam ends it at Glamsterdam.
  --
  -- So EthLib takes the BPO forks too, as version 4 of the method that checks a payload does.
  | 3, fork => decide (.dencun ≤ fork) && decide (fork < .glamsterdam)
  -- Version 4, step 1.2: Amsterdam, here Glamsterdam, which the update by Bogota ends at Hegotá.
  | 4, fork => fork == .glamsterdam
  -- Version 5, step 1.2: Bogota, the execution side of Hegotá.
  | _, fork => fork == .hegota

/-- The fork of the structure of the payload attributes whose timestamp is in a fork. -/
def attributesForkAt (fork : Fork) : Fork :=
  -- `PayloadAttributesV1` before Shapella.
  if fork < .shapella then .paris
  -- Version 2, parameter 2: `PayloadAttributesV2` from Shapella.
  else if fork < .dencun then .shapella
  -- `PayloadAttributesV3` from Dencun.
  else if fork < .glamsterdam then .dencun
  -- `PayloadAttributesV4` from Glamsterdam.
  else if fork < .hegota then .glamsterdam
  -- `PayloadAttributesV5` from Hegotá.
  else .hegota

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

/-- The fork of the structure has the inclusion list exactly when the fork has it. -/
theorem hegota_le_attributesForkAt_iff (fork : Fork) :
    .hegota ≤ attributesForkAt fork ↔ .hegota ≤ fork := by
  cases fork <;> decide

/-- Payload attributes of the structure of a fork, as attributes of that fork, field by field. -/
def PayloadAttributes.ofStructure {fork : Fork} (a : PayloadAttributes (attributesForkAt fork)) :
    PayloadAttributes fork where
  timestamp := a.timestamp
  prevRandao := a.prevRandao
  suggestedFeeRecipient := a.suggestedFeeRecipient
  withdrawals := a.withdrawals.congr (shapella_le_attributesForkAt_iff fork)
  parentBeaconBlockRoot := a.parentBeaconBlockRoot.congr (dencun_le_attributesForkAt_iff fork)
  slotNumber := a.slotNumber.congr (glamsterdam_le_attributesForkAt_iff fork)
  targetGasLimit := a.targetGasLimit.congr (glamsterdam_le_attributesForkAt_iff fork)
  inclusionListTransactions :=
    a.inclusionListTransactions.congr (hegota_le_attributesForkAt_iff fork)

/-- Payload attributes at a fork, when their structure is that of the fork.

Otherwise there are none. -/
def PayloadAttributes.atFork (a : Σ f, PayloadAttributes f) (fork : Fork) :
    Option (PayloadAttributes fork) :=
  if h : attributesForkAt fork = a.1 then some (PayloadAttributes.ofStructure (h ▸ a.2)) else none

/-- The checks of decoded payload attributes against the head that they build on.

The result is the attributes at their fork. -/
def checkAttributes (config : ChainConfig) (version : Nat) (head : KnownPayload)
    (attributes : Σ f, PayloadAttributes f) :
    Except EngineError (Σ fork, PayloadAttributes fork) := do
  -- The number and the time of the head are unbounded, as its header holds them.
  --
  -- The fork of the attributes is the active fork at the number after the head and at their time.
  let timestamp := attributes.2.timestamp
  -- A timestamp in the time frame of no fork gives `-38005`.
  let some fork := config.activeFork (head.number + 1) timestamp.toNat
    | throw (.unsupportedFork none)
  -- Version 3, step 2.2, and versions 4 and 5, step 1.2: a fork that the version does not take.
  --
  -- That is `-38005`, as the updates by later forks also give to earlier versions.
  --
  -- The source does not order this check and step 8.1, and EthLib runs this one first.
  unless attributesTakeFork version fork do throw (.unsupportedFork (some fork))
  -- Version 2, parameter 2: `PayloadAttributesV1` before Shapella, `PayloadAttributesV2` from it.
  --
  -- Only version 2 takes two structures, and the wrong version of the structure gives `-38003`.
  let some atFork := PayloadAttributes.atFork attributes fork | throw .invalidPayloadAttributes
  -- Step 8.1: the timestamp of the attributes is greater than that of the head, else `-38003`.
  unless head.timestamp < timestamp.toNat do throw .invalidPayloadAttributes
  return ⟨fork, atFork⟩

/-- A version of the method: its status, the new head, and the payload attributes of a build.

Version 0 reads as 1, and a version above 5 reads as 5. -/
def forkchoiceUpdatedCall (config : ChainConfig) (transition : TransitionConfiguration)
    (version : Nat) (tree : PayloadTree) (finalized : Option Hash32) (params : Json) :
    Except EngineError
      (PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)) := do
  -- The versions of the method are 1 to 5; the C export passes no other.
  --
  -- The configuration of the transition gives the terminal total difficulty.
  let (state, attributes) ← forkchoiceUpdatedParams version params
  -- Steps 1 to 5 and 7: the status, and the head when the state is updated to it.
  let (status, head) ← forkchoiceUpdated transition tree finalized state
  match attributes, head with
  -- Step 8: the attributes count once the state is applied with a `VALID` head.
  | some j, some h =>
    -- The attributes fit a structure of the version, then pass the checks against the head.
    --
    -- Step 8.3: a failed check keeps the state applied.
    --
    -- EthLib holds no state, so the error carries no head.
    let decoded ← payloadAttributesOfVersion version j
    -- The update applies only a head that the tree holds, so this branch never runs.
    let some known := tree.lookup h | return (status, head, none)
    -- Step 8.2: attributes that pass every check begin a build on the head.
    --
    -- EthLib returns them, as those of the fork of their timestamp, and the response gives the ID.
    return (status, head, some (← checkAttributes config version known decoded))
  -- Without attributes or an applied head, no build begins, so the attributes change nothing.
  | _, _ => return (status, head, none)

/-- The bytes of one inclusion list transaction in the input of a payload ID. -/
def inclusionListEntryBytes (transaction : ByteArray) : List UInt8 :=
  -- Each byte of the transaction comes after a byte 1, and a byte 0 ends the transaction.
  --
  -- So the bytes of a list of transactions give back the list, whatever the lengths.
  --
  -- A byte 2 after them marks the end of the list.
  transaction.data.toList.flatMap (fun b => [1, b]) ++ [0]

/-- The bytes that the ID of a build hashes: the head, then the attributes of their fork.

The source leaves the form of the ID to the client, so this layout is EthLib's own. -/
def payloadIdInput (head : Hash32) (attributes : PayloadAttributes fork) : ByteArray :=
  -- Each number takes 8 big-endian bytes.
  let word (n : UInt64) : List UInt8 := (Base.ByteOrder.toBE 8 n.toNat).toList
  -- From Shapella, each withdrawal gives its four fields in turn.
  let withdrawals : List UInt8 := if h : .shapella ≤ fork then
      (attributes.withdrawals h).flatMap fun w =>
        word w.index ++ word w.validatorIndex ++ w.address.toList ++ word w.amount
    else []
  -- From Dencun, the root of the parent beacon block.
  let beacon : List UInt8 :=
    if h : .dencun ≤ fork then (attributes.parentBeaconBlockRoot h).toList else []
  -- From Glamsterdam, the slot and then the target gas limit.
  let glamsterdam : List UInt8 := if h : .glamsterdam ≤ fork then
      word (attributes.slotNumber h) ++ word (attributes.targetGasLimit h)
    else []
  -- From Hegotá, each transaction of the inclusion list in a form that marks where it ends.
  --
  -- A byte 2 then ends the list, so the list and the bytes after it split in one way only.
  let hegota : List UInt8 := if h : .hegota ≤ fork then
      (attributes.inclusionListTransactions h).flatMap inclusionListEntryBytes ++ [2]
    else []
  -- The head, the timestamp, the RANDAO mix and the fee recipient.
  --
  -- Then the inclusion list, the withdrawals, the root, the slot and the target gas limit.
  ⟨(head.toList ++ word attributes.timestamp ++ attributes.prevRandao.toList ++
    attributes.suggestedFeeRecipient.toList ++ hegota ++ withdrawals ++ beacon ++
    glamsterdam).toArray⟩

/-- The ID of the build that attributes start on a head: the first 8 bytes of a Keccak-256 hash.

Step 5 of the [payload building][build] of Paris gives each new build its own ID.

[build]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payload-building
-/
def payloadId (head : Hash32) (attributes : PayloadAttributes fork) : PayloadId :=
  -- Payload building, step 5: each new build has its own ID.
  --
  -- EthLib hashes the head and then the attributes, each number in 8 big-endian bytes.
  --
  -- The same head and attributes give the same ID.
  --
  -- In an update, the configuration, the tree, the head and the timestamp fix the fork.
  --
  -- So within an update, other attributes or another head give other bytes to hash.
  --
  -- So distinct builds of an update get distinct IDs unless their hashes share the first 8 bytes.
  let digest := Cryptography.Hash.Keccak.keccak256 (payloadIdInput head attributes)
  Vector.ofFn fun i => digest[i.val]'(by
    have := i.isLt
    simp only [Cryptography.Hash.Keccak.DIGEST_LEN_256]
    omega)

/-! ## The response -/

/-- The response of a call, from its result: the status, and the ID of the build that it begins.

These are the answers of step 9 of [`engine_forkchoiceUpdatedV1`][fcu] that are not errors.

[fcu]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_forkchoiceupdatedv1 -/
def forkchoiceUpdatedResponse
    (result : PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)) :
    PayloadStatus × Option PayloadId :=
  -- Step 9: the payload ID names the build once it has begun, and is `null` otherwise.
  --
  -- The ID is that of the applied head and the attributes, when the call returns attributes.
  (result.1, result.2.1.bind fun head => result.2.2.map fun a => payloadId head a.2)

/-- Whether a status is one that a forkchoice update answers: valid, invalid or syncing.

`RestrictedPayloadStatusV1` of [`payload.yaml`][schema] and [step 9][fcu] allow only these.

[schema]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/openrpc/schemas/payload.yaml
[fcu]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_forkchoiceupdatedv1 -/
def Status.restricted : Status → Bool
  -- Response: the status is restricted to `VALID`, `INVALID` and `SYNCING`.
  | .valid | .invalid | .syncing => true
  -- The method never answers the two other statuses of `PayloadStatusV1`.
  | .accepted | .invalidBlockHash => false

/-- The response as JSON: the payload status, and the payload ID or `null`. -/
def forkchoiceUpdatedResponseJson (status : PayloadStatus) (validationError : Option String)
    (id : Option PayloadId) : Json :=
  -- Response: `payloadStatus`, then `payloadId` as `DATA` of 8 bytes or `null`.
  Json.mkObj [("payloadStatus", payloadStatusJson status validationError),
    ("payloadId", optionJson (dataJson ·.toList) id)]

/-- A forkchoice response read from its JSON: one of three statuses, and an ID.

The decoder does not check the pairing of status, hash and ID that step 9 asks of a client. -/
def forkchoiceUpdatedResponseOfJson (j : Json) :
    Decode (PayloadStatus × Option String × Option PayloadId) := do
  -- A field whose value is `null` counts as absent.
  let fs ← fields "forkchoiceUpdatedResponse" j
  -- Response: the object has `payloadStatus` and `payloadId`, and EthLib rejects another field.
  unless fs.all (["payloadStatus", "payloadId"].contains ·.1) do
    invalid "forkchoiceUpdatedResponse: unknown field"
  let (status, validationError) ←
    payloadStatusOfJson (← field "forkchoiceUpdatedResponse" fs "payloadStatus")
  -- Response: the status is one of the three that the method answers.
  unless status.status.restricted do invalid "payloadStatus: not a status of the method"
  -- Response: `payloadId` is `DATA` of 8 bytes or `null`, and EthLib reads a missing one as `null`.
  let id ← Json.lift ((fs.lookup "payloadId").mapM (fixed "payloadId" 8))
  return (status, validationError, id)

/-- The response of version 5 as JSON: a payload status of version 2, and the ID or `null`.

Step 2 of [`engine_forkchoiceUpdatedV5`][fcu5] gives the inclusion list verdict.

[fcu5]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#engine_forkchoiceupdatedv5 -/
def forkchoiceUpdatedResponseV2Json (status : PayloadStatus) (validationError : Option String)
    (inclusionListSatisfied : Option Bool) (id : Option PayloadId) : Json :=
  -- The verdict comes as given, and the function after this one pairs it with the status.
  --
  -- Version 5, response: `PayloadStatusV2` with `inclusionListSatisfied`, then `payloadId`.
  Json.mkObj [("payloadStatus", payloadStatusV2Json status validationError inclusionListSatisfied),
    ("payloadId", optionJson (dataJson ·.toList) id)]

/-- The inclusion list verdict of a version 5 response, from whether the head satisfies its list. -/
def inclusionListVerdict (status : PayloadStatus) (satisfied : Bool) : Option Bool :=
  -- Version 5, step 2.1: for a `VALID` head, whether it satisfied the inclusion list constraints.
  --
  -- Version 5, step 2.3: otherwise `null`.
  if status.status = .valid then some satisfied else none

end EthLib.Engine
