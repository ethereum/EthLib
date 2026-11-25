module

public import EthLib.Base.ChainConfig
public import EthLib.Engine.Block
public import EthLib.Engine.Json
public import EthLib.Engine.TransitionConfiguration
public import EthLib.Execution.Blocks.Transition

/-!
# `Engine.NewPayload`

The checks of `engine_newPayload`, versions 1 to 6, and the status that each payload gets.

Sources, at commit `1ca0818` of execution-apis:

- versions [1][v1], [2][v2], [3][v3], [4][v4], [5][v5] and [6][v6] of the method
- the updates of earlier versions by [Cancun][cancun], [Prague][prague] and [Osaka][osaka]
- the updates of version 4 by [Amsterdam][amsterdam] and of version 5 by [Bogota][bogota]

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_newpayloadv1
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#engine_newpayloadv2
[cancun]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#update-the-methods-of-previous-forks
[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#engine_newpayloadv3
[prague]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/prague.md#update-the-methods-of-previous-forks
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/prague.md#engine_newpayloadv4
[osaka]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#prague-api
[amsterdam]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#update-the-methods-of-previous-forks
[v5]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_newpayloadv5
[v6]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#engine_newpayloadv6
[bogota]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/bogota.md#update-the-methods-of-previous-forks
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Rpc (withdrawal versionedHash versionedHashJson)
open EthLib.Cryptography.Kzg (VersionedHash)

/-- Whether a version of the method takes payloads of a fork. -/
def acceptsFork (version : Nat) (fork : Fork) : Bool :=
  -- A step names the version of the method, as in version 3, step 2.
  --
  -- The Engine API calls the execution side of Glamsterdam by the name Amsterdam.
  match version with
  -- Version 1 states no range of forks.
  --
  -- EthLib takes Paris only, so a payload of any other fork is an unsupported fork, `-38005`.
  | 1 => fork == .paris
  -- Version 2: the forks before Cancun, by the update in `cancun.md`, here Paris and Shapella.
  --
  -- Version 2, step 3 moves payloads from Shanghai on to version 2.
  | 2 => fork == .paris || fork == .shapella
  -- Version 3, step 2: the time frame of Cancun, here Dencun.
  | 3 => fork == .dencun
  -- Version 4, step 1: the time frame of Prague, here Pectra.
  --
  -- The update by Osaka widens step 1 to the time frame of Prague or Osaka, here Fusaka too.
  --
  -- The update by Amsterdam rejects payloads from Amsterdam on.
  --
  -- So here it takes every fork from Pectra before Glamsterdam, BPO1 to BPO5 included.
  | 4 => decide (.pectra ≤ fork) && decide (fork < .glamsterdam)
  -- Version 5, step 1: the time frame of Amsterdam, here Glamsterdam.
  --
  -- The update by Bogota ends it at Bogota, here Hegota.
  | 5 => fork == .glamsterdam
  -- The Engine API calls the execution side of Hegotá by the name Bogota.
  --
  -- Version 6, step 1: the time frame of Bogota, here Hegota.
  | 6 => fork == .hegota
  -- No other version of the method exists.
  | _ => false

/-- The number of parameters of a version of the method. -/
def paramCount (version : Nat) : Nat :=
  -- Version 6 takes five parameters, versions 4 and 5 four, and version 3 three.
  --
  -- Versions 1 and 2 take one, the payload.
  if version ≥ 6 then 5 else if version ≥ 4 then 4 else if version = 3 then 3 else 1

/-- Whether a version of the method takes a version of the payload structure.

Version 5 reads its structure, version 4, with its own decoder. -/
def acceptsStructure (version layout : Nat) : Bool :=
  match version with
  -- Version 1 takes `ExecutionPayloadV1`.
  | 1 => layout == 1
  -- Version 2 takes `ExecutionPayloadV1` or `ExecutionPayloadV2`.
  --
  -- Which of the two the fork needs is checked once the fork is known.
  | 2 => layout == 1 || layout == 2
  -- Versions 3 and 4 take `ExecutionPayloadV3`, and another version fails the fork check later.
  | _ => layout == 3

/-- The payload of a version of the method, with its access list and its slot from version 5. -/
def payloadParam (version : Nat) (j : Json) :
    Decode (AnyPayload × Option (ByteArray × UInt64)) := do
  if version ≥ 5 then
    -- Versions 5 and 6 take `ExecutionPayloadV4`, which appends `blockAccessList` and `slotNumber`.
    --
    -- Version 5, step 2: a missing `blockAccessList` is an invalid parameter, `-32602`.
    --
    -- A missing `slotNumber` is `-32602` too, by the strict match of version 3, step 1.
    let (any, blockAccessList, slotNumber) ← payloadV4 j
    return (any, some (blockAccessList, slotNumber))
  else
    let any ← anyPayload j
    -- Another structure than the version takes is an invalid parameter, `-32602`.
    --
    -- Version 2 and step 1 of version 3 state that code, and EthLib gives it for version 1 too.
    unless acceptsStructure version any.version do
      invalid s!"payload: version {any.version} of the structure"
    return (any, none)

/-- The parameters of a version of the method, each decoded. -/
def newPayloadParams (version : Nat) (params : Json) :
    Decode (AnyPayload × Option (ByteArray × UInt64) × Option (List VersionedHash) ×
      Option Hash32 × Option (List ByteArray)) := do
  -- Version 3, step 1: the parameters strictly match those of the version, or `-32602`.
  --
  -- A `null` value counts as not provided, so it fails the match too.
  --
  -- Versions 1 and 2 state no such step, and EthLib checks them the same way.
  let params ← match params with
    | .arr items => pure items.toList
    | _ => invalid "params: not an array"
  unless params.length == paramCount version ∧ params.all (!·.isNull) do
    invalid s!"params: not {paramCount version} values"
  let param (i : Nat) : Except EngineError Json :=
    match params[i]? with
    | some j => pure j
    | none => invalid s!"params: no value {i}"
  -- Parameter 1: the payload, with its access list and its slot from version 5.
  let (any, amsterdam) ← payloadParam version (← param 0)
  -- Parameter 2, from version 3: `expectedBlobVersionedHashes`, an array of 32-byte data.
  let hashes ← if version ≥ 3 then
    some <$> array "expectedBlobVersionedHashes" (versionedHash "versioned hash") (← param 1)
    else pure none
  -- Parameter 3, from version 3: `parentBeaconBlockRoot`, 32 bytes of data.
  let beaconRoot ← if version ≥ 3 then
    some <$> fixed "parentBeaconBlockRoot" 32 (← param 2) else pure none
  -- Parameter 4, from version 4: `executionRequests`, an array of data.
  let requests ← if version ≥ 4 then
    some <$> array "executionRequests" (bytes "request") (← param 3) else pure none
  -- Parameter 5, from version 6: `inclusionListTransactions`, an array of data.
  --
  -- Version 6, step 4: a malformed transaction rejects no payload, so any byte string reads.
  --
  -- The checks here use the list no further.
  --
  -- Whether a payload satisfies it needs the execution rules of Bogota, which this library lacks.
  --
  -- So steps 2 and 3 of version 6 are not modelled: the status has no inclusion-list field.
  if version ≥ 6 then
    let _ ← inclusionListOfJson (← param 4)
  return (any, amsterdam, hashes, beaconRoot, requests)

/-- The parameters of a version of the method as JSON, in the order that the version takes. -/
def newPayloadParamsJson {fork : Fork} (version : Nat) (payload : ExecutionPayload fork)
    (amsterdam : Option (ByteArray × UInt64)) (hashes : List VersionedHash) (beaconRoot : Hash32)
    (requests : List ByteArray) : Json :=
  -- The consensus layer writes the parameters of each version as JSON, in this order.
  --
  -- A valid request has a version that takes the fork of the payload.
  --
  -- It gives the access list and the slot exactly from version 5.
  --
  -- Parameter 1: `ExecutionPayloadV4` with a list and a slot, else the structure of the fork.
  let payload := match amsterdam with
    | some (accessList, slot) => executionPayloadV4Json payload accessList slot
    | none => executionPayloadJson payload
  -- Parameters 2 and 3 from version 3, then parameter 4 from version 4.
  .arr ([payload] ++
    (if 3 ≤ version then [listJson versionedHashJson hashes, dataJson beaconRoot.toList]
      else []) ++
    (if 4 ≤ version then [listJson (dataJson ·.data.toList) requests] else [])).toArray

/-- The parameters of version 6, from Bogota: those of version 5, then an inclusion list. -/
def newPayloadV6Params (params : Json) :
    Decode ((AnyPayload × Option (ByteArray × UInt64) × Option (List VersionedHash) ×
      Option Hash32 × Option (List ByteArray)) × List ByteArray) := do
  -- The five parameters of version 6, none of them `null`.
  let six ← newPayloadParams 6 params
  -- Parameter 5, the inclusion list, which the line above has read already.
  let inclusionList ← match params with
    | .arr items => inclusionListOfJson (items[4]?.getD .null)
    | _ => invalid "params: not an array"
  return (six, inclusionList)

/-- The parameters of version 6 as JSON: those of version 5, then the inclusion list. -/
def newPayloadV6ParamsJson {fork : Fork} (payload : ExecutionPayload fork)
    (amsterdam : ByteArray × UInt64) (hashes : List VersionedHash) (beaconRoot : Hash32)
    (requests : List ByteArray) (inclusionList : List ByteArray) : Json :=
  -- The parameters of version 5 are an array, and the inclusion list goes at its end.
  match newPayloadParamsJson 5 payload (some amsterdam) hashes beaconRoot requests with
  | .arr items => .arr (items.push (inclusionListJson inclusionList))
  | other => other

/-- Whether request lists have more than one byte each, with strictly increasing types. -/
def validRequests : List ByteArray → Bool
  -- Version 4, parameter 4: with no element, the array is `[]`.
  | [] => true
  -- Version 4, step 3: an element of 1 byte or shorter is an invalid parameter.
  | [r] => r.size > 1
  | r :: s :: rest =>
    match r[0]?, s[0]? with
    -- Each element is longer than 1 byte, and its first byte is its type.
    --
    -- The types strictly increase, so no element is out of order and no two share a type.
    | some a, some b => r.size > 1 && s.size > 1 && a < b && validRequests (s :: rest)
    -- An empty element has no type, and is too short.
    | _, _ => false

/-- A payload that passed the checks of a version of the method: the block at its fork. -/
structure CheckedBlock (version : Nat) where
  /-- The fork of the payload. -/
  fork : Fork
  /-- The version takes payloads of the fork. -/
  accepted : acceptsFork version fork = true
  /-- The block of the payload. -/
  block : Block fork Transaction

/-- The checks of a version of the method, under a chain configuration, before execution.

The result is a JSON-RPC error, the invalid status with its reason, or the block of the payload. -/
def checkNewPayload (config : ChainConfig) (version : Nat) (params : Json) :
    Except EngineError (Except (PayloadStatus × PayloadError) (CheckedBlock version)) := do
  -- The parameters of the version, or `-32602`.
  let (any, amsterdam, hashes, beaconRoot, requests) ← newPayloadParams version params
  -- Version 4, step 3: an element out of order, too short or of a repeated type is `-32602`.
  --
  -- Versions 5 and 6 follow the specification of version 4, so the rule holds for them too.
  --
  -- Version 6 restates the order of the elements in its parameter 4, without the error.
  if let some requests := requests then
    unless validRequests requests do invalid "executionRequests: out of order or too short"
  -- The fork of the payload is the active fork at its number and its timestamp.
  --
  -- The source reads the timestamp alone, and EthLib reads the number too for forks by block.
  let number := any.common.blockNumber.toNat
  let timestamp := any.common.timestamp.toNat
  -- A payload before every fork is an unsupported fork too.
  let some fork := config.activeFork number timestamp | throw (.unsupportedFork none)
  -- The version takes the fork of the payload, or `-38005`.
  if hAccepted : acceptsFork version fork = true then
    -- The structure of the fork, or `-32602`.
    --
    -- Version 2: `ExecutionPayloadV1` before Shanghai, and `ExecutionPayloadV2` from it.
    let payload ← any.atFork fork
    -- Parameter 3 is given exactly from Dencun, and parameter 4 exactly from Pectra.
    --
    -- The access list and the slot are given exactly from Glamsterdam.
    --
    -- These hold once the version takes the fork.
    let beacon ← since (f := .dencun) "parentBeaconBlockRoot" beaconRoot
    let requests ← since (f := .pectra) "executionRequests" requests
    let accessList ← since (f := .glamsterdam) "blockAccessList" (amsterdam.map (·.1))
    let slot ← since (f := .glamsterdam) "slotNumber" (amsterdam.map (·.2))
    -- Version 1 defines the statuses.
    --
    -- Version 1, step 6: a failed check of the payload alone is `INVALID`, with a null hash.
    let invalidStatus (e : PayloadError) : PayloadStatus × PayloadError :=
      match e with
      -- A failed block hash is `INVALID_BLOCK_HASH` in version 1.
      --
      -- Version 2, step 2: `INVALID` supplants it.
      | .wrongBlockHash .. =>
        (⟨if version = 1 then .invalidBlockHash else .invalid, none⟩, e)
      | _ => (⟨.invalid, none⟩, e)
    -- Version 1, steps 1 and 2, with the additions of versions 4 and 5: the block of the payload.
    --
    -- The module of the block marks those steps.
    match payload.toBlock beacon requests accessList slot with
    | .error e => return .error (invalidStatus e)
    | .ok block =>
      -- Version 3, step 3.1: the actual array is the versioned hashes of the blob transactions.
      --
      -- Step 3.2: `INVALID` with a null hash when the expected and the actual arrays differ.
      --
      -- EthLib runs it after the block hash, so only the reason differs from the source's order.
      if let some hashes := hashes then
        if ExecutionPayload.blobVersionedHashes block.transactions ≠ hashes then
          let actual := ExecutionPayload.blobVersionedHashes block.transactions
          return .error (invalidStatus (.wrongVersionedHashes hashes actual))
      return .ok ⟨fork, hAccepted, block⟩
  else throw (.unsupportedFork (some fork))

/-- The status of `engine_newPayload` from an execution layer without the parent's state. -/
def newPayloadWithoutState (config : ChainConfig) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) := do
  match ← checkNewPayload config version params with
  -- Version 1, step 6: a payload that fails the checks is `INVALID` or `INVALID_BLOCK_HASH`.
  | .error (status, reason) => return (status, some reason)
  -- Steps 3 and 6: validation needs the parent's state, which is missing, so `SYNCING`.
  --
  -- EthLib never answers `ACCEPTED` here, which needs the ancestors of the payload.
  | .ok _ => return (⟨.syncing, none⟩, none)

/-- Whether the parent of a payload passes the terminal block check, given its total difficulty.

The check is step 2 of the payload validation of Paris.

It follows the [transition block validity][eip3675] of EIP-3675.

[eip3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#transition-block-validity
-/
def passesTerminalCheck (transition : TransitionConfiguration) (totalDifficulty : Nat)
    (parent : RecentBlock) : Bool :=
  -- A parent from Paris on is no block of proof of work, so it passes.
  --
  -- A total below the difficulty is not that of a real chain, so such a parent fails.
  decide (.paris ≤ parent.fork) || (decide (parent.header.difficulty ≤ totalDifficulty) &&
    -- EIP-3675: a terminal PoW block has a total difficulty of at least the terminal one.
    --
    -- Its own parent has a total below it, its total minus its difficulty.
    isTerminalPowBlock transition totalDifficulty (totalDifficulty - parent.header.difficulty))

/-- The status of `engine_newPayload` from an execution layer that holds the parent's state.

It runs the [payload validation][validation] of Paris.

[validation]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payload-validation
-/
def newPayloadOnChain (transition : TransitionConfiguration) (totalDifficulty : Nat)
    (chain : BlockChain) (version : Nat) (params : Json) :
    Except EngineError
      (PayloadStatus × Option PayloadError × Option (RecentBlock × Execution.State.State)) := do
  match ← checkNewPayload chain.config version params with
  -- Version 1, step 6: a payload that fails the checks is `INVALID` or `INVALID_BLOCK_HASH`.
  | .error (status, reason) => return (status, some reason, none)
  | .ok checked =>
    let header := checked.block.header
    -- The chain holds the state after its last recent block, whose total difficulty is given.
    --
    -- Steps 3 and 6: without the parent's state, the payload is `SYNCING`.
    let some parent := chain.recent.getLast? | return (⟨.syncing, none⟩, none, none)
    -- The chain holds only the state after its last block, so another parent is `SYNCING` too.
    --
    -- The method holds no invalid block, so a child of an invalid payload is syncing here.
    --
    -- A node that keeps its invalid blocks answers that such a child is invalid.
    unless parent.header.hash.toOption = some header.parentHash do
      return (⟨.syncing, none⟩, none, none)
    -- Payload validation, step 2: the most recent PoW ancestor satisfies the terminal conditions.
    --
    -- Else `INVALID`, with the zero hash as the latest valid hash.
    --
    -- Only a PoW parent is checked: the chain is taken as valid, its terminal block included.
    --
    -- Version 2, step 1 lets a node skip the check, and EthLib runs it for every version.
    unless passesTerminalCheck transition totalDifficulty parent do
      return (⟨.invalid, some 0⟩, some (.invalidTerminalBlock header.parentHash), none)
    -- Version 1, step 4 and payload validation, step 3: the block runs on the parent's state.
    --
    -- No seal check: the block validity of EIP-3675 removes the Ethash checks.
    match stateTransition chain checked.block (checkSeal := false) with
    -- Payload validation, step 3: `VALID`, with the block hash of the payload as latest valid hash.
    --
    -- A valid payload also gives its block, as the new last recent block, and the state after it.
    | .ok post =>
      return (⟨.valid, header.hash.toOption⟩, none, some (⟨checked.fork, header, []⟩, post))
    -- An execution that aborts, such as on missing code, gives no verdict, so `SYNCING`.
    | .error (.aborted _) => return (⟨.syncing, none⟩, none, none)
    -- Payload validation, step 3: `INVALID`, with the latest valid ancestor, here the parent.
    --
    -- A parent before Paris is a PoW block, so the hash is zero.
    | .error e =>
      let ancestor : Hash32 := if parent.fork < .paris then 0 else header.parentHash
      return (⟨.invalid, some ancestor⟩, some (.invalidBlock e), none)

end EthLib.Engine
