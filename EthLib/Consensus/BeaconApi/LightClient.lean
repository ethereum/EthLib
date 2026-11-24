module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.ForkDigest
public import EthLib.Consensus.LightClient.FullNode
public import EthLib.Consensus.ReqResp.Messages

/-!
# `Consensus.BeaconApi.LightClient`

The answers of the Beacon API that serve a light client.

The [bootstrap] of a block comes from the block and its post state, which the store holds.

The [updates] of a range of periods are the best updates that the node knows.

The node chooses which update is the best of a period, so the caller gives them.

The source does not fix one answer for a range.

So a predicate gives every answer that the source accepts, and one function gives the longest.

The other accepted answers are the nonempty starts of the longest one.

The [finality update] and the [optimistic update] are the latest that the node knows.

SOUNDNESS.md records the points that the source leaves open.

[bootstrap]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/light_client/bootstrap.yaml
[updates]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/light_client/updates.yaml
[finality update]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/light_client/finality_update.yaml
[optimistic update]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/light_client/optimistic_update.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Bootstrap -/

/-- The error of a block whose bootstrap the node cannot serve, with code 404. -/
def noBootstrap (root : Root) : ErrorMessage :=
  -- The source: code 404; the message is EthLib's.
  { code := 404, message := s!"No bootstrap for block {toHex root.toArray}" }

/-- The bootstrap of a block of the store, from the block and its post state. -/
def bootstrapFor (config : Config) (store : Store preset fork) (root : Root) :
    Except ErrorMessage (LightClientBootstrap preset fork) :=
  -- The source: to fulfil a request, the post state of the block must be known.
  match store.blocks[root]?, store.blockStates[root]? with
  | some block, some state =>
    -- EthLib's choice: a block whose slot is of another fork than the store's gives code 404.
    if config.forkAtEpoch (computeEpochAtSlot preset block.slot) ≠ fork then
      .error (noBootstrap root)
    else
      -- The source: the bootstrap of the block, which only a block from Altair has.
      --
      -- It reads only the message of the block, so the signature is left at zero.
      --
      -- The source: a bootstrap that cannot be produced gives code 404.
      (createLightClientBootstrap config state ⟨block, Vector.replicate 96 0⟩).mapError
        fun _ => noBootstrap root
  -- A block or a post state that the store lacks gives code 404 too.
  | _, _ => .error (noBootstrap root)

/-- The response of the bootstrap endpoint, with the version of the store's fork. -/
def bootstrapResponse (config : Config) (store : Store preset fork) (root : Root) :
    Except ErrorMessage ApiEnvelope :=
  -- The source: the version and the bootstrap under the data key.
  versioned fork (bootstrapFor config store root)

/-! ## Updates -/

/-- Whether an answer to an updates request is one that the source accepts.

The node knows at most one update per period, in a map from periods.

The source also bounds the range by the period of the head, which the known updates leave out. -/
def IsUpdatesAnswer {α : Type} (known : Std.TreeMap UInt64 α) (startPeriod count : UInt64)
    (answer : List α) : Prop :=
  ∃ periods : List UInt64,
    -- Each entry is the known update of its period.
    periods.map (known[·]?) = answer.map some ∧
      -- The source: each period is in the range, start <= p < start + count.
      (∀ period ∈ periods, InCountRange startPeriod count period) ∧
      -- The source: results in consecutive order by period, which EthLib reads as no gap.
      (∀ i (h : i + 1 < periods.length), periods[i + 1].toNat = periods[i].toNat + 1) ∧
      -- The source: at least the earliest known result in the range, so the answer starts there.
      --
      -- The source does not ask for every known update of the range.
      (∀ period, InCountRange startPeriod count period → period ∈ known →
        ∃ first, periods.head? = some first ∧ first ≤ period) ∧
      -- The source: at most min(128, count) results.
      answer.length ≤ lightClientUpdatesLimit count

/-- The known updates of the periods from a period on, with a bound on how many it reads. -/
def updatesFrom {α : Type} (known : Std.TreeMap UInt64 α) (startPeriod count : UInt64) :
    Nat → Nat → List α
  -- The bound is reached.
  | _, 0 => []
  | period, bound + 1 =>
    -- The period must fit in 64 bits and lie in the range.
    if period < UInt64.size ∧ InCountRange startPeriod count (UInt64.ofNat period) then
      match known[UInt64.ofNat period]? with
      -- Its update, then those of the next periods.
      | some update => update :: updatesFrom known startPeriod count (period + 1) bound
      -- The periods have no gap, so a period that the node lacks ends the answer.
      | none => []
    -- A period past the range ends the answer.
    else []

/-- The known updates of the range from its earliest known period, with no gap, cut to the limit.

It is empty when the range has no known update. -/
def updatesInRange {α : Type} (known : Std.TreeMap UInt64 α) (startPeriod count : UInt64) :
    List α :=
  -- The earliest known period of the range, as the map lists its periods in increasing order.
  match known.toList.find? (fun entry => decide (InCountRange startPeriod count entry.1)) with
  -- The source: at least that one, in consecutive order, at most min(128, count).
  --
  -- EthLib gives the longest such answer.
  | some (first, _) =>
    updatesFrom known startPeriod count first.toNat (lightClientUpdatesLimit count)
  | none => []

/-- An update of a light client, with its fork. -/
abbrev AnyLightClientUpdate (preset : Preset) : Type :=
  (fork : Fork) × LightClientUpdate preset fork

/-- The JSON form of the updates answer: one object per update, with its version and its data. -/
def updatesJson (updates : List (AnyLightClientUpdate preset)) : Except ErrorMessage Json := do
  let items ← updates.mapM fun ⟨fork, update⟩ => do
    -- An update that cannot be written gives code 500.
    let data ← apiJsonOr500 update
    -- The source: an array of objects, each with the version of its update and the update.
    return Json.mkObj ((fork.consensusVersion?.map fun v => ("version", Json.str v.name)).toList ++
      [("data", data)])
  return Json.arr items.toArray

/-- Why the SSZ chunks of updates cannot be built or read. -/
inductive ChunkError where
  /-- The fork of an update has no light client. -/
  | forkNotSpecified (fork : Fork)
  /-- The fork of an update is not the fork of the epoch of its attested header. -/
  | forkMismatch (fork expected : Fork)
  /-- A digest or an encoding could not be computed, or a payload does not decode. -/
  | ssz (fault : Err)
  /-- A chunk is too long for its length field of eight bytes. -/
  | tooLong (length : Nat)
  /-- The bytes end inside a chunk.

  The error gives the offset of the chunk, the length it needs from there, and the length left. -/
  | truncated (offset needed available : Nat)
  /-- A chunk is shorter than its digest. -/
  | shortChunk (length : Nat)
  /-- No fork of the configuration has the digest of a chunk. -/
  | unknownDigest (digest : ForkDigest)
  /-- The digest of a chunk is not the digest of the epoch of its update's attested header.

  The error gives the digest of the chunk, then the digest of that epoch. -/
  | digestMismatch (digest expected : ForkDigest)
  deriving Repr

/-- The epoch of the attested header of an update, which selects the digest of its chunk. -/
def contextEpoch (update : LightClientUpdate preset fork) : Epoch :=
  -- The source: the epoch of the slot of the beacon header of the attested header.
  --
  -- The source: it may differ from the fork of the signature slot, which verifies the aggregate.
  computeEpochAtSlot preset update.attestedHeader.beacon.slot

/-- Nothing when an update is of the fork of the epoch of its attested header, from Altair. -/
def checkUpdateFork (config : Config) (update : LightClientUpdate preset fork) :
    Except ChunkError Unit := do
  -- The source: the genesis fork version has no update type.
  unless .altair ≤ fork do throw (.forkNotSpecified fork)
  -- The fork of the update is the fork that its context epoch selects.
  let expected := config.forkAtEpoch (contextEpoch update)
  unless fork = expected do throw (.forkMismatch fork expected)

/-- The SSZ chunk of an update: the length of the rest, the fork digest, then the update. -/
def encodeUpdateChunk (config : Config) (genesisValidatorsRoot : Root)
    (update : LightClientUpdate preset fork) : Except ChunkError ByteArray := do
  -- The update must be of the fork of its context epoch, from Altair.
  checkUpdateFork config update
  -- The source: the context is the 4-byte fork digest of the context epoch.
  let digest ← (computeForkDigest config genesisValidatorsRoot (contextEpoch update)).mapError .ssz
  -- The source: the payload is the SSZ serialization of the update.
  let payload ← (SszType.serialize update).mapError .ssz
  -- The response chunk is the context, then the payload.
  let rest := ⟨digest.toArray⟩ ++ payload
  -- Its length must fit in 64 bits.
  unless rest.size < 2 ^ 64 do throw (.tooLong rest.size)
  -- The source: the byte length of the response chunk, as a little-endian Uint64, comes first.
  return ⟨(ByteOrder.toLE 8 rest.size).toArray⟩ ++ rest

/-- The SSZ body of the updates answer: the chunks of the updates, one after another. -/
def encodeUpdateChunks (config : Config) (genesisValidatorsRoot : Root)
    (updates : List (AnyLightClientUpdate preset)) : Except ChunkError ByteArray :=
  -- The source: a sequence of zero or more chunks, one update each, in the order of the answer.
  updates.foldlM (fun out ⟨_, update⟩ => do
    return out ++ (← encodeUpdateChunk config genesisValidatorsRoot update)) ByteArray.empty

/-- The updates of SSZ chunks, read from a position of the bytes to their end. -/
def decodeUpdateChunksFrom (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (data : ByteArray) (start : Nat) : Except ChunkError (List (AnyLightClientUpdate preset)) :=
  -- The end of the bytes ends the sequence of chunks.
  if _done : data.size ≤ start then .ok []
  else if header : start + 8 ≤ data.size then
    -- The source: the byte length of the chunk, a little-endian Uint64.
    let length := ByteOrder.ofLE (Vector.ofFn fun (i : Fin 8) => data[start + i]'(by omega))
    -- A chunk holds at least its 4-byte context.
    if short : length < 4 then .error (.shortChunk length)
    else if inside : start + 8 + length ≤ data.size then do
      -- The source: the context, a 4-byte fork digest.
      let digest : ForkDigest := Vector.ofFn fun (i : Fin 4) => data[start + 8 + i]'(by omega)
      -- The digest selects the fork of the response type.
      let some epoch := forkOfDigest config genesisValidatorsRoot digest
        | throw (.unknownDigest digest)
      let fork := config.forkAtEpoch epoch
      -- The source: the genesis fork version has no update type.
      unless .altair ≤ fork do throw (.forkNotSpecified fork)
      -- The source: the payload, the SSZ serialization of an update of that fork.
      let payload := data.extract (start + 12) (start + 8 + length)
      let update ← (SszType.deserialize (LightClientUpdate preset fork) payload).mapError .ssz
      -- The digest must be the digest of the context epoch of that update.
      let expected ←
        (computeForkDigest config genesisValidatorsRoot (contextEpoch update)).mapError .ssz
      unless expected = digest do throw (.digestMismatch digest expected)
      -- The next chunk starts after this one.
      let rest ← decodeUpdateChunksFrom preset config genesisValidatorsRoot data
        (start + 8 + length)
      return ⟨fork, update⟩ :: rest
    -- The bytes end inside the chunk.
    else .error (.truncated start (8 + length) (data.size - start))
  -- The bytes end inside the length.
  else .error (.truncated start 8 (data.size - start))
termination_by data.size - start
decreasing_by omega

/-- The updates of the SSZ body of an updates answer, each with the fork its digest names. -/
def decodeUpdateChunks (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (data : ByteArray) : Except ChunkError (List (AnyLightClientUpdate preset)) :=
  decodeUpdateChunksFrom preset config genesisValidatorsRoot data 0

/-! ## Finality and optimistic updates -/

/-- The error of a node that knows no update of a kind, with code 404. -/
def noLatestUpdate (kind : String) : ErrorMessage :=
  -- The source: code 404 when no update is available; the message is EthLib's.
  { code := 404, message := s!"No {kind} update is available" }

/-- The response of the finality update endpoint, from the latest update that the node knows. -/
def finalityUpdateResponse (latest : Option (LightClientUpdate preset fork)) :
    Except ErrorMessage ApiEnvelope :=
  match latest with
  -- EthLib derives the latest finality update from the latest update that the node knows.
  | some update => versioned fork (.ok (createLightClientFinalityUpdate update))
  -- The source: a node that knows none gives code 404.
  | none => .error (noLatestUpdate "finality")

/-- The response of the optimistic update endpoint, from the latest update that the node knows. -/
def optimisticUpdateResponse (latest : Option (LightClientUpdate preset fork)) :
    Except ErrorMessage ApiEnvelope :=
  match latest with
  -- EthLib derives the latest optimistic update from the latest update that the node knows.
  | some update => versioned fork (.ok (createLightClientOptimisticUpdate update))
  -- The source: a node that knows none gives code 404.
  | none => .error (noLatestUpdate "optimistic")

end EthLib.Consensus.BeaconApi
