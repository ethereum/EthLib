module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.ForkDigest
public import EthLib.Consensus.LightClient.FullNode

/-!
# `Consensus.BeaconApi.LightClient`

The answers of the Beacon API that serve a light client.

The [bootstrap] of a block comes from the block and its post state, which the store holds.

The [updates] of a range of periods are the best updates that the node knows.

The node chooses which update is the best of a period, so the caller gives them.

The answer holds the known updates of the range in increasing period order.

It holds at most the smaller of 128 and the count.

The source does not ask for every known update of the range.

It asks that the answer start with the earliest one.

So a predicate gives every answer that the source accepts, and one function gives the longest.

In SSZ, the updates come as chunks: a length of eight bytes, a fork digest and the update.

The digest is that of the epoch of the attested header, and it names the fork of the update.

The [finality update] and the [optimistic update] are the latest that the node knows.

When it knows none, the answer is the error with code 404.

SOUNDNESS.md records the points that the source leaves open.

[bootstrap]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/light_client/bootstrap.yaml
[updates]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/light_client/updates.yaml
[finality update]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/light_client/finality_update.yaml
[optimistic update]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/light_client/optimistic_update.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Bootstrap -/

/-- The error of a block whose bootstrap the node cannot serve, with code 404. -/
def noBootstrap (root : Root) : ErrorMessage :=
  { code := 404, message := s!"No bootstrap for block {toHex root.toArray}" }

/-- The bootstrap of a block of the store, from the block and its post state.

The bootstrap reads only the message of the block, so the signature is left at zero.

The answer is the error with code 404 when the store lacks the block or its state.

It is the same error when the store's fork is not the fork of the block's slot.

It is the same error again when the bootstrap cannot be built, as for a block before Altair. -/
def bootstrapFor (config : Config) (store : Store preset fork) (root : Root) :
    Except ErrorMessage (LightClientBootstrap preset fork) :=
  match store.blocks[root]?, store.blockStates[root]? with
  | some block, some state =>
    if config.forkAtEpoch (computeEpochAtSlot preset block.slot) ≠ fork then
      .error (noBootstrap root)
    else
      (createLightClientBootstrap config state ⟨block, Vector.replicate 96 0⟩).mapError
        fun _ => noBootstrap root
  | _, _ => .error (noBootstrap root)

/-- The response of the bootstrap endpoint, with the version of the store's fork. -/
def bootstrapResponse (config : Config) (store : Store preset fork) (root : Root) :
    Except ErrorMessage ApiEnvelope :=
  versioned fork (bootstrapFor config store root)

/-! ## Updates -/

/-- Whether a period is in the range of a request: from the start, for the count of periods.

The bound is computed without overflow. -/
def InRange (startPeriod count period : UInt64) : Prop :=
  startPeriod.toNat ≤ period.toNat ∧ period.toNat < startPeriod.toNat + count.toNat

instance (startPeriod count period : UInt64) : Decidable (InRange startPeriod count period) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The most updates an answer may hold: the smaller of the request limit and the count. -/
def updatesLimit (count : UInt64) : Nat :=
  min MAX_REQUEST_LIGHT_CLIENT_UPDATES.toNat count.toNat

/-- Whether an answer to an updates request is one that the source accepts.

The node knows at most one update per period, in a map from periods.

Each entry is the known update of a period of the range, and the periods increase strictly.

When the range has a known update, the answer starts with that of the earliest such period.

The answer holds at most the limit of entries.

The source also bounds the range by the period of the head, which the known updates leave out. -/
def IsUpdatesAnswer {α : Type} (known : Std.TreeMap UInt64 α) (startPeriod count : UInt64)
    (answer : List α) : Prop :=
  ∃ periods : List UInt64,
    periods.map (known[·]?) = answer.map some ∧
      (∀ period ∈ periods, InRange startPeriod count period) ∧
      periods.Pairwise (· < ·) ∧
      (∀ period, InRange startPeriod count period → period ∈ known →
        ∃ first, periods.head? = some first ∧ first ≤ period) ∧
      answer.length ≤ updatesLimit count

/-- The known updates of the range, in increasing period order, cut to the limit. -/
def updatesInRange {α : Type} (known : Std.TreeMap UInt64 α) (startPeriod count : UInt64) :
    List α :=
  ((known.toList.filter fun entry => decide (InRange startPeriod count entry.1)).take
    (updatesLimit count)).map (·.2)

/-- An update of a light client, with its fork. -/
abbrev AnyLightClientUpdate (preset : Preset) : Type :=
  (fork : Fork) × LightClientUpdate preset fork

/-- The JSON form of the updates answer: one object per update, with its version and its data. -/
def updatesJson (updates : List (AnyLightClientUpdate preset)) : Except ErrorMessage Json := do
  let items ← updates.mapM fun ⟨fork, update⟩ => do
    let data ← apiJsonOr500 update
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
  /-- The bytes end inside a chunk. -/
  | truncated
  /-- A chunk is shorter than its digest. -/
  | shortChunk (length : Nat)
  /-- No fork of the configuration has the digest of a chunk. -/
  | unknownDigest (digest : ForkDigest)
  /-- The digest of a chunk is not the digest of the epoch of its update's attested header. -/
  | digestMismatch (digest : ForkDigest)
  deriving Repr

/-- The epoch of the attested header of an update, which selects the digest of its chunk. -/
def contextEpoch (update : LightClientUpdate preset fork) : Epoch :=
  computeEpochAtSlot preset update.attestedHeader.beacon.slot

/-- Nothing when an update is of the fork of the epoch of its attested header, from Altair. -/
def checkUpdateFork (config : Config) (update : LightClientUpdate preset fork) :
    Except ChunkError Unit := do
  unless .altair ≤ fork do throw (.forkNotSpecified fork)
  let expected := config.forkAtEpoch (contextEpoch update)
  unless fork = expected do throw (.forkMismatch fork expected)

/-- The SSZ chunk of an update: the length of the rest, the fork digest, then the update.

The length is a little-endian integer of eight bytes.

The digest is that of the epoch of the attested header.

The update must be of the fork of that epoch, from Altair. -/
def encodeUpdateChunk (config : Config) (genesisValidatorsRoot : Root)
    (update : LightClientUpdate preset fork) : Except ChunkError ByteArray := do
  checkUpdateFork config update
  let digest ← (computeForkDigest config genesisValidatorsRoot (contextEpoch update)).mapError .ssz
  let payload ← (SszType.serialize update).mapError .ssz
  let rest := ⟨digest.toArray⟩ ++ payload
  unless rest.size < 2 ^ 64 do throw (.tooLong rest.size)
  return ⟨(uintToBytes 8 rest.size).toArray⟩ ++ rest

/-- The SSZ body of the updates answer: the chunks of the updates, one after another. -/
def encodeUpdateChunks (config : Config) (genesisValidatorsRoot : Root)
    (updates : List (AnyLightClientUpdate preset)) : Except ChunkError ByteArray :=
  updates.foldlM (fun out ⟨_, update⟩ => do
    return out ++ (← encodeUpdateChunk config genesisValidatorsRoot update)) ByteArray.empty

/-- The updates of SSZ chunks, read from a position of the bytes to their end.

Each chunk names its fork by its digest, and the payload decodes as an update of that fork.

The digest must be the digest of the epoch of the attested header of that update. -/
def decodeUpdateChunksFrom (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (data : ByteArray) (start : Nat) : Except ChunkError (List (AnyLightClientUpdate preset)) :=
  if _done : data.size ≤ start then .ok []
  else if header : start + 8 ≤ data.size then
    let length := bytesToUint (Vector.ofFn fun (i : Fin 8) => data[start + i]'(by omega))
    if short : length < 4 then .error (.shortChunk length)
    else if inside : start + 8 + length ≤ data.size then do
      let digest : ForkDigest := Vector.ofFn fun (i : Fin 4) => data[start + 8 + i]'(by omega)
      let some epoch := forkOfDigest config genesisValidatorsRoot digest
        | throw (.unknownDigest digest)
      let fork := config.forkAtEpoch epoch
      unless .altair ≤ fork do throw (.forkNotSpecified fork)
      let payload := data.extract (start + 12) (start + 8 + length)
      let update ← (SszType.deserialize (LightClientUpdate preset fork) payload).mapError .ssz
      let expected ←
        (computeForkDigest config genesisValidatorsRoot (contextEpoch update)).mapError .ssz
      unless expected = digest do throw (.digestMismatch digest)
      let rest ← decodeUpdateChunksFrom preset config genesisValidatorsRoot data
        (start + 8 + length)
      return ⟨fork, update⟩ :: rest
    else .error .truncated
  else .error .truncated
termination_by data.size - start
decreasing_by omega

/-- The updates of the SSZ body of an updates answer, each with the fork its digest names. -/
def decodeUpdateChunks (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (data : ByteArray) : Except ChunkError (List (AnyLightClientUpdate preset)) :=
  decodeUpdateChunksFrom preset config genesisValidatorsRoot data 0

/-! ## Finality and optimistic updates -/

/-- The error of a node that knows no update of a kind, with code 404. -/
def noLatestUpdate (kind : String) : ErrorMessage :=
  { code := 404, message := s!"No {kind} update is available" }

/-- The response of the finality update endpoint, from the latest update that the node knows. -/
def finalityUpdateResponse (latest : Option (LightClientUpdate preset fork)) :
    Except ErrorMessage ApiEnvelope :=
  match latest with
  | some update => versioned fork (.ok (createLightClientFinalityUpdate update))
  | none => .error (noLatestUpdate "finality")

/-- The response of the optimistic update endpoint, from the latest update that the node knows. -/
def optimisticUpdateResponse (latest : Option (LightClientUpdate preset fork)) :
    Except ErrorMessage ApiEnvelope :=
  match latest with
  | some update => versioned fork (.ok (createLightClientOptimisticUpdate update))
  | none => .error (noLatestUpdate "optimistic")

end EthLib.Consensus.BeaconApi
