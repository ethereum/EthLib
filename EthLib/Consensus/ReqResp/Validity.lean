module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.LightClient.Containers
public import EthLib.Consensus.ReqResp.Messages
public import EthLib.Consensus.Signing

/-!
# `Consensus.ReqResp.Validity`

When the response of a request and response protocol is valid for its request.

Each check reads only the request and the items of the response.

So the rules that need the chain of the responder stay out, such as sending the first block it has.

The check of inclusion lists also reads the committee of their slot, which the caller computes.

## Blocks by range

The request names the slots from its start slot, for its count of slots.

- The response has at most as many blocks as the count, and at most the request limit of the fork.
- Each block lies in the requested slots.
- Each block has a higher slot than the one before it.
- When the step is 1, each block names the one before it as its parent.

The step must be 1; for any other step, the range of slots stays the same.

## Blocks by root

The request names blocks by the roots of their messages.

- The response has at most as many blocks as the request has roots.
- The root of each block is one of the requested roots.

## Blocks by head

From Fulu, a request names the blocks along the ancestry of a block root, that block first.

- The response has at most as many blocks as the count, and at most the request limit of Deneb.
- The root of its first block is the requested root.
- Each block is the parent of the block before it, and has a lower slot.

So the slots of the blocks decrease along the whole list.

The walk also stops before an ancestor outside the epochs that clients must serve.

That rule needs the current epoch, so it stays out with the rule that asks for at least one block.

A block item carries no fork, so the check does not compare the context bytes of a chunk.

## Light client updates by range

From Altair, a request names the light client updates of a range of sync committee periods.

The period of an update is the period of the slot of its attested header.

- The response has at most as many updates as the count, and at most 128.
- The period of each update lies in the requested periods.
- Each update has the period after the period of the update before it.
- The epoch of the attested header of each update is from Altair.
- The context bytes of the chunk of each update are the fork digest of that epoch.

The digest is computed with the root of the genesis validators of the chain.

From Fulu, it changes with the blob parameters too, so it tells apart more epochs than the fork.

The receiver decodes the payload with the type of the fork that the digest names.

So the check reads the digest, and not a fork that the receiver may have read from it.

A server returns the updates in consecutive order by period.

EthLib reads that as periods with no gap, so a server that lacks a period stops there.

A server returns at least its earliest known update of the range, which may come after the start.

The check cannot see which periods the server knows.

So the first update may have any period of the range.

## Light client bootstrap

From Altair, a request names the bootstrap of a block by the root of that block.

The root of a bootstrap is the root of the beacon header of its header.

- The response has at most one bootstrap.
- Its root is the requested root.
- The epoch of its header is from Altair.
- The context bytes of its chunk are the fork digest of that epoch.

It does not check the header or the branch of the sync committee, which the light client checks.

## Sidecars by range

From Deneb, a request names the blob sidecars of a range of slots.

From Fulu, a request names the column sidecars of a range of slots, for some columns.

Each check assumes a fork at which its protocol exists.

- The response has at most the count times the most sidecars of one block.
- It has at most the request limit, which is the most sidecars of the most blocks.
- Each sidecar lies in the requested slots.
- The sidecars are in increasing order of slot, then of index.
- The sidecars of one slot name the same block.
- For blobs, the indices of the sidecars of one block are 0, 1, 2 and so on.
- For blobs, each index is below the most blobs of one block.
- For columns, each block has each requested column once, and no other.
- For columns, each index is below the number of columns.

A response holds every sidecar of each block it serves, but a blob check cannot see how many.

So any block of a blob response may lack its last blobs.

## Sidecars by root

The request names sidecars by the root of their block and their index.

- The response has at most as many sidecars as the request names.
- Each sidecar is one that the request names.

The protocol does not forbid a sidecar twice in one response, so these checks allow it.

## Payload envelopes

From Gloas, a request names the payload envelopes of a range of slots, or of some block roots.

The rules of a range follow those of blocks by range.

- The response has at most as many envelopes as the count, and at most the request limit.
- Each envelope lies in the requested slots, with slots that increase.
- The payload of each envelope names the payload before it as its parent.

That last rule holds because the envelopes come from one chain.

A block that the chain leaves without its payload gives no envelope.

The next payload then builds on the last payload of the chain.

By root, the response has at most as many envelopes as requested roots.

The block root of each envelope is one of the requested roots.

## Inclusion lists by indices

From Heze, a request names the inclusion lists of a slot, by seats of its committee.

The committee is the inclusion list committee of the slot, on the chain of the dependent root.

A list names the root that fixes its committee, so a list for the request names its dependent root.

A validator may hold several seats, so a seat count bounds the lists, and a list may repeat.

- The response has at most as many lists as requested seats, and at most the request limit.
- Each list has the requested slot and dependent root.
- The validator of each list holds a requested seat of the committee.

[EIP-4844] adds the blob protocols, and [EIP-7594] the column protocols.

[EIP-7732] adds the payload envelopes, and [EIP-7805] the inclusion lists.

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#networking
[EIP-7594]: https://eips.ethereum.org/EIPS/eip-7594#networking
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#p2p-changes
[EIP-7805]: https://eips.ethereum.org/EIPS/eip-7805#p2p-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- What a response check reads from a block: its slot, the root of its parent and its own root.

The blocks of one response can belong to several forks, and this form is the same for each. -/
structure ResponseBlock where
  /-- The slot of the block. -/
  slot : Slot
  /-- The root of the parent block. -/
  parentRoot : Root
  /-- The root of the block, without its signature. -/
  root : Root
  deriving DecidableEq, Repr

/-- What a response check reads from a signed block.

It fails when the root of the block cannot be computed. -/
def ResponseBlock.ofSigned {preset : Preset} {fork : Fork} (block : SignedBeaconBlock preset fork) :
    Except Err ResponseBlock := do
  -- The root of the message of the block, which leaves out the signature.
  let root ← SszType.hashTreeRoot block.message
  return { slot := block.message.slot, parentRoot := block.message.parentRoot, root }

/-- Whether a relation holds between each item of a list and the item after it. -/
def allAdjacent {α : Type} (r : α → α → Bool) : List α → Bool
  -- `r a b` for the first two items `a` and `b`, and the same on the list from `b`.
  | a :: tail@(b :: _) => r a b && allAdjacent r tail
  -- A list of fewer than two items has no such pair.
  | _ => true

/-- Whether each block of a list has a higher slot than the block before it. -/
def ResponseBlock.slotsAscending (blocks : List ResponseBlock) : Bool :=
  -- The slot of each block is below the slot of the block after it.
  allAdjacent (fun a b => a.slot < b.slot) blocks

/-- Whether each block of a list names the block before it as its parent. -/
def ResponseBlock.parentsLinked (blocks : List ResponseBlock) : Bool :=
  -- The parent root of each block is the root of the block before it.
  allAdjacent (fun a b => b.parentRoot == a.root) blocks

/-- Whether a slot is one that a request for blocks by range names. -/
def BeaconBlocksByRangeRequest.containsSlot (request : BeaconBlocksByRangeRequest)
    (slot : Slot) : Bool :=
  -- `x ≤ s < x + n`, for the start slot `x`, the count `n` and the slot `s`.
  decide (InCountRange request.startSlot request.count slot)

/-- Whether the blocks of a response are valid for a request for blocks by range.

The fork is the one in effect when the request is served; it sets the request limit. -/
def isValidBlocksByRangeResponse (config : Config) (fork : Fork)
    (request : BeaconBlocksByRangeRequest) (blocks : List ResponseBlock) : Bool :=
  -- At most as many blocks as the count of the request.
  blocks.length ≤ request.count.toNat &&
    -- At most the request limit of blocks at the fork.
    blocks.length ≤ (config.maxRequestBlocks fork).toNat &&
    -- Each block lies in the requested slots.
    blocks.all (fun block => request.containsSlot block.slot) &&
    -- The slots of the blocks increase.
    ResponseBlock.slotsAscending blocks &&
    -- When the step is 1, each block names the block before it as its parent.
    (request.step != 1 || ResponseBlock.parentsLinked blocks)

/-- Whether the blocks of a response are valid for a request for blocks by root. -/
def isValidBlocksByRootResponse {config : Config} {fork : Fork}
    (request : BeaconBlocksByRootRequest config fork) (blocks : List ResponseBlock) : Bool :=
  -- At most as many blocks as requested roots, and the root of each block is a requested root.
  blocks.length ≤ request.data.size && blocks.all (fun block => request.data.contains block.root)

/-- Whether each block of a list is the parent of the block before it, at a lower slot. -/
def ResponseBlock.ancestryLinked (blocks : List ResponseBlock) : Bool :=
  -- For each block `a` and the block `b` after it, `b` has a lower slot and is the parent of `a`.
  allAdjacent (fun a b => b.slot < a.slot && a.parentRoot == b.root) blocks

/-- Whether the blocks of a response are valid for a request for blocks by head.

The request limit is the one of Deneb, whatever the fork that serves the request. -/
def isValidBlocksByHeadResponse (config : Config) (request : BeaconBlocksByHeadRequest)
    (blocks : List ResponseBlock) : Bool :=
  -- At most as many blocks as the count, and at most `MAX_REQUEST_BLOCKS_DENEB`.
  blocks.length ≤ request.count.toNat &&
    blocks.length ≤ config.MAX_REQUEST_BLOCKS_DENEB.toNat &&
    -- The root of the first block, if any, is the requested root.
    blocks.head?.all (fun first => first.root == request.beaconRoot) &&
    -- Each block is the parent of the block before it, at a lower slot.
    ResponseBlock.ancestryLinked blocks

/-- What a response check reads from a light client update: its attested slot and its digest.

The attested slot is the slot of the attested header of the update.

The digest is the fork digest that the context bytes of the chunk of the update carry. -/
structure ResponseUpdate where
  /-- The slot of the attested header. -/
  attestedSlot : Slot
  /-- The fork digest that the context bytes of the chunk carry. -/
  digest : ForkDigest
  deriving DecidableEq, Repr

/-- What a response check reads from a light client update, sent with a digest. -/
def ResponseUpdate.ofUpdate {preset : Preset} {fork : Fork}
    (update : LightClientUpdate preset fork) (digest : ForkDigest) : ResponseUpdate :=
  -- The slot of the beacon header of the attested header, and the digest of the chunk.
  { attestedSlot := update.attestedHeader.beacon.slot, digest }

/-- The sync committee period of an update: the period of the slot of its attested header. -/
def ResponseUpdate.period (preset : Preset) (update : ResponseUpdate) : UInt64 :=
  -- Let `s` be the attested slot.
  --
  -- The period is `floor(floor(s / SLOTS_PER_EPOCH) / EPOCHS_PER_SYNC_COMMITTEE_PERIOD)`.
  computeSyncCommitteePeriodAtSlot preset update.attestedSlot

/-- Whether the digest of a light client chunk is the fork digest of the epoch of a slot. -/
def lightClientDigestMatches (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (slot : Slot) (digest : ForkDigest) : Bool :=
  -- The epoch `e` of the slot.
  let epoch := computeEpochAtSlot preset slot
  -- The fork at `e` is from Altair, which adds light clients.
  .altair ≤ config.forkAtEpoch epoch &&
    -- The digest is the fork digest of `e`, under the root of the genesis validators of the chain.
    --
    -- A digest that cannot be computed matches nothing.
    (computeForkDigest config genesisValidatorsRoot epoch).toOption == some digest

/-- Whether the digest of an update is the fork digest of the epoch of its attested header. -/
def ResponseUpdate.digestMatches (preset : Preset) (config : Config)
    (genesisValidatorsRoot : Root) (update : ResponseUpdate) : Bool :=
  -- The digest of the update matches at its attested slot.
  lightClientDigestMatches preset config genesisValidatorsRoot update.attestedSlot update.digest

/-- Whether the updates of a response are valid for a request for light client updates by range. -/
def isValidLightClientUpdatesByRangeResponse (preset : Preset) (config : Config)
    (genesisValidatorsRoot : Root) (request : LightClientUpdatesByRangeRequest)
    (updates : List ResponseUpdate) : Bool :=
  -- At most `min(MAX_REQUEST_LIGHT_CLIENT_UPDATES, n)` updates, for the count `n`.
  updates.length ≤ lightClientUpdatesLimit request.count &&
    -- The period of each update lies in the requested periods, and its digest matches.
    updates.all (fun update =>
      decide (InCountRange request.startPeriod request.count (update.period preset)) &&
        update.digestMatches preset config genesisValidatorsRoot) &&
    -- Each update has period `p + 1`, for the period `p` of the update before it.
    allAdjacent (fun a b => (b.period preset).toNat == (a.period preset).toNat + 1) updates

/-- What a response check reads from a light client bootstrap: its slot, its root and its digest.

The slot and the root are those of the beacon header of its header.

The digest is the fork digest that the context bytes of the chunk of the bootstrap carry. -/
structure ResponseBootstrap where
  /-- The slot of the header. -/
  slot : Slot
  /-- The root of the beacon header of the header. -/
  root : Root
  /-- The fork digest that the context bytes of the chunk carry. -/
  digest : ForkDigest
  deriving DecidableEq, Repr

/-- What a response check reads from a light client bootstrap, sent with a digest.

It fails when the root of the beacon header cannot be computed. -/
def ResponseBootstrap.ofBootstrap {preset : Preset} {fork : Fork}
    (bootstrap : LightClientBootstrap preset fork) (digest : ForkDigest) :
    Except Err ResponseBootstrap := do
  -- The slot and the root of the beacon header of the header of the bootstrap.
  let header := bootstrap.header.beacon
  let root ← SszType.hashTreeRoot header
  return { slot := header.slot, root, digest }

/-- Whether the bootstraps of a response are valid for a request for a light client bootstrap.

The request is the root of the block whose bootstrap it asks for. -/
def isValidLightClientBootstrapResponse (preset : Preset) (config : Config)
    (genesisValidatorsRoot : Root) (request : Root) (bootstraps : List ResponseBootstrap) : Bool :=
  -- At most one bootstrap.
  bootstraps.length ≤ 1 &&
    -- Its root is the requested root, and its digest matches at its slot.
    bootstraps.all (fun bootstrap =>
      bootstrap.root == request &&
        lightClientDigestMatches preset config genesisValidatorsRoot bootstrap.slot
          bootstrap.digest)

/-- What a response check reads from a sidecar: the slot and root of its block, and its index.

The index is the index of the blob for a blob sidecar, and of the column for a column sidecar. -/
structure ResponseSidecar where
  /-- The slot of the block. -/
  slot : Slot
  /-- The root of the block, without its signature. -/
  blockRoot : Root
  /-- The index of the sidecar in its block. -/
  index : UInt64
  deriving DecidableEq, Repr

/-- What a response check reads from a blob sidecar.

It fails when the root of the header cannot be computed. -/
def ResponseSidecar.ofBlob {preset : Preset} (sidecar : BlobSidecar preset) :
    Except Err ResponseSidecar := do
  -- The slot and the root of the header of the block, and the index of the blob.
  let header := sidecar.signedBlockHeader.message
  let blockRoot ← SszType.hashTreeRoot header
  return { slot := header.slot, blockRoot, index := sidecar.index }

/-- What a response check reads from a column sidecar.

Before Gloas, it fails when the root of the header cannot be computed. -/
def ResponseSidecar.ofColumn {preset : Preset} {fork : Fork}
    (sidecar : DataColumnSidecar preset fork) : Except Err ResponseSidecar :=
  -- From Gloas, the sidecar carries the slot and the root of its block.
  if gloas : .glamsterdam ≤ fork then
    return ⟨sidecar.slot gloas, sidecar.beaconBlockRoot gloas, sidecar.index⟩
  else do
    -- Before Gloas, they are the slot and the root of the header of the block.
    let header := (sidecar.signedBlockHeader (Nat.lt_of_not_le gloas)).message
    let blockRoot ← SszType.hashTreeRoot header
    return { slot := header.slot, blockRoot, index := sidecar.index }

/-- Whether a blob sidecar may follow another in a response by range. -/
def ResponseSidecar.nextBlob (a b : ResponseSidecar) : Bool :=
  -- At one slot, `b` is the next blob of the same block: index `i + 1`, for the index `i` of `a`.
  if a.slot = b.slot then b.blockRoot == a.blockRoot && b.index.toNat == a.index.toNat + 1
  -- Otherwise `b` is at a later slot, and is the first blob of its block, at index 0.
  else a.slot < b.slot && b.index == 0

/-- Whether a column sidecar may follow another in a response by range. -/
def ResponseSidecar.nextColumn (a b : ResponseSidecar) : Bool :=
  -- At one slot, `b` is a later column of the same block.
  --
  -- Otherwise `b` belongs to a block at a later slot.
  if a.slot = b.slot then b.blockRoot == a.blockRoot && a.index < b.index else a.slot < b.slot

/-- Whether the sidecars of a response are valid for a request for blob sidecars by range.

The fork is the one in effect when the request is served; it sets the limits.

Served under Electra, the check allows the Electra count of blobs, even at an older slot.

From Fulu no new blob sidecars exist, so the Electra count stays the limit.

The request limit is the most blobs of the most blocks, taken without overflow. -/
def isValidBlobSidecarsByRangeResponse (config : Config) (fork : Fork)
    (request : BlobSidecarsByRangeRequest) (sidecars : List ResponseSidecar) : Bool :=
  -- Let `m` be the most blobs of one block at the fork, and `n` the count of the request.
  --
  -- At most `n * m` sidecars, in natural numbers.
  sidecars.length ≤ request.count.toNat * (blobSidecarLimit config fork).toNat &&
    -- At most `MAX_REQUEST_BLOCKS_DENEB * m` sidecars, in natural numbers.
    sidecars.length ≤
      config.MAX_REQUEST_BLOCKS_DENEB.toNat * (blobSidecarLimit config fork).toNat &&
    -- Each sidecar lies in the requested slots, with an index below `m`.
    sidecars.all (fun sidecar =>
      decide (InCountRange request.startSlot request.count sidecar.slot) &&
        sidecar.index.toNat < (blobSidecarLimit config fork).toNat) &&
    -- The first sidecar, if any, has index 0.
    sidecars.head?.all (fun first => first.index == 0) &&
    -- Each sidecar is the next blob of its block, or the first blob of a block at a later slot.
    allAdjacent ResponseSidecar.nextBlob sidecars

/-- Whether the sidecars of a response are valid for a request for blob sidecars by root. -/
def isValidBlobSidecarsByRootResponse {config : Config} {fork : Fork}
    (request : BlobSidecarsByRootRequest config fork) (sidecars : List ResponseSidecar) : Bool :=
  -- At most as many sidecars as the request names.
  --
  -- The block root and the index of each sidecar are a pair that the request names.
  sidecars.length ≤ request.data.size &&
    sidecars.all (fun sidecar => request.data.contains ⟨sidecar.blockRoot, sidecar.index⟩)

/-- The sidecars of a response grouped by slot: each group is a longest run with one slot. -/
def ResponseSidecar.groupBySlot (sidecars : List ResponseSidecar) : List (List ResponseSidecar) :=
  -- Two adjacent sidecars fall in one group when they have one slot.
  sidecars.splitBy (fun a b => a.slot == b.slot)

/-- Whether the sidecars of a response are valid for a request for column sidecars by range.

A response holds every sidecar of each block it serves; here that means every requested column.

The request limit is the most sidecars of the most blocks, taken without overflow. -/
def isValidDataColumnSidecarsByRangeResponse (preset : Preset) (config : Config)
    (request : DataColumnSidecarsByRangeRequest preset) (sidecars : List ResponseSidecar) : Bool :=
  -- Let `N` be `NUMBER_OF_COLUMNS` and `n` the count of the request.
  --
  -- At most `n * N` sidecars, and at most `MAX_REQUEST_BLOCKS_DENEB * N`, in natural numbers.
  sidecars.length ≤ request.count.toNat * preset.NUMBER_OF_COLUMNS.toNat &&
    sidecars.length ≤ config.MAX_REQUEST_BLOCKS_DENEB.toNat * preset.NUMBER_OF_COLUMNS.toNat &&
    -- Each sidecar lies in the requested slots, with an index below `N` that the request names.
    sidecars.all (fun sidecar =>
      decide (InCountRange request.startSlot request.count sidecar.slot) &&
        sidecar.index < preset.NUMBER_OF_COLUMNS && request.columns.data.contains sidecar.index) &&
    -- Each sidecar is a later column of its block, or belongs to a block at a later slot.
    allAdjacent ResponseSidecar.nextColumn sidecars &&
    -- The sidecars of each slot hold each requested column.
    (ResponseSidecar.groupBySlot sidecars).all (fun block =>
      request.columns.data.all (fun column => block.any (·.index == column)))

/-- The number of column sidecars that a request by root names. -/
def DataColumnSidecarsByRootRequest.columnCount {preset : Preset} {config : Config}
    (request : DataColumnSidecarsByRootRequest preset config) : Nat :=
  -- The sum, over the identifiers of the request, of their numbers of columns.
  (request.data.map (·.columns.data.size)).sum

/-- Whether the sidecars of a response are valid for a request for column sidecars by root. -/
def isValidDataColumnSidecarsByRootResponse {preset : Preset} {config : Config}
    (request : DataColumnSidecarsByRootRequest preset config)
    (sidecars : List ResponseSidecar) : Bool :=
  -- At most as many sidecars as the request names columns.
  sidecars.length ≤ request.columnCount &&
    -- Each sidecar has the block root and one of the columns of an identifier of the request.
    sidecars.all (fun sidecar => request.data.any (fun identifier =>
      identifier.blockRoot == sidecar.blockRoot && identifier.columns.data.contains sidecar.index))

/-- What a response check reads from a payload envelope, from Gloas.

It reads the slot and the hash of the payload, the hash of its parent and the root of its block. -/
structure ResponseEnvelope where
  /-- The slot of the payload.

  For a valid envelope it is the slot of its block. -/
  slot : Slot
  /-- The root of the beacon block whose bid the payload fulfils. -/
  beaconBlockRoot : Root
  /-- The hash of the parent execution block. -/
  parentHash : Hash32
  /-- The hash of the execution block. -/
  blockHash : Hash32
  deriving DecidableEq, Repr

/-- What a response check reads from a signed payload envelope, from Gloas. -/
def ResponseEnvelope.ofSigned {preset : Preset} {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (envelope : SignedExecutionPayloadEnvelope preset fork) : ResponseEnvelope :=
  -- The slot of the payload, the root of the block, and the parent hash and hash of the payload.
  let payload := envelope.message.payload
  ⟨payload.slotNumber gloas, envelope.message.beaconBlockRoot, payload.parentHash,
    payload.blockHash⟩

/-- Whether a payload envelope may follow another in a response by range. -/
def ResponseEnvelope.next (a b : ResponseEnvelope) : Bool :=
  -- `b` has a higher slot, and the parent hash of its payload is the hash of the payload of `a`.
  a.slot < b.slot && b.parentHash == a.blockHash

/-- Whether the envelopes of a response are valid for a request for payload envelopes by range.

The fork is the one in effect when the request is served; it sets the request limit. -/
def isValidExecutionPayloadEnvelopesByRangeResponse (config : Config) (fork : Fork)
    (request : ExecutionPayloadEnvelopesByRangeRequest) (envelopes : List ResponseEnvelope) :
    Bool :=
  -- At most as many envelopes as the count, and at most the request limit of blocks at the fork.
  envelopes.length ≤ request.count.toNat &&
    envelopes.length ≤ (config.maxRequestBlocks fork).toNat &&
    -- Each envelope lies in the requested slots.
    envelopes.all (fun envelope =>
      decide (InCountRange request.startSlot request.count envelope.slot)) &&
    -- The slots increase, and each payload names the payload before it as its parent.
    allAdjacent ResponseEnvelope.next envelopes

/-- Whether the envelopes of a response are valid for a request for payload envelopes by root. -/
def isValidExecutionPayloadEnvelopesByRootResponse {config : Config}
    (request : ExecutionPayloadEnvelopesByRootRequest config)
    (envelopes : List ResponseEnvelope) : Bool :=
  -- At most as many envelopes as requested roots, and the block root of each is a requested root.
  envelopes.length ≤ request.data.size &&
    envelopes.all (fun envelope => request.data.contains envelope.beaconBlockRoot)

/-- The number of seats that a request asks for, which bounds the number of its lists. -/
def InclusionListsByIndicesRequest.listCount {preset : Preset}
    (request : InclusionListsByIndicesRequest preset) : Nat :=
  -- The number of set bits.
  request.indices.bits.count true

/-- Whether a validator holds a seat of a committee that a request asks for. -/
def InclusionListsByIndicesRequest.asksFor {preset : Preset}
    (request : InclusionListsByIndicesRequest preset) (committee : InclusionListCommittee preset)
    (validator : ValidatorIndex) : Bool :=
  -- Some seat `i` of the committee has bit `i` set and holds the validator.
  (request.indices.bits.zip committee).any fun (asked, member) => asked && member == validator

/-- Whether the lists of a response are valid for a request for inclusion lists by indices.

The committee is the inclusion list committee of the slot, on the chain of the dependent root. -/
def isValidInclusionListsByIndicesResponse {preset : Preset} (config : Config)
    (request : InclusionListsByIndicesRequest preset) (committee : InclusionListCommittee preset)
    (lists : List InclusionList) : Bool :=
  -- At most as many lists as requested seats, and at most `MAX_REQUEST_INCLUSION_LIST`.
  lists.length ≤ request.listCount &&
    lists.length ≤ config.MAX_REQUEST_INCLUSION_LIST.toNat &&
    -- Each list has the requested slot and dependent root.
    --
    -- Its validator holds a requested seat.
    lists.all fun list =>
      list.slot == request.slot && list.dependentRoot == request.dependentRoot &&
        request.asksFor committee list.validatorIndex

end EthLib.Consensus
