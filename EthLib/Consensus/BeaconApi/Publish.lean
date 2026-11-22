module

public import EthLib.Consensus.BeaconApi.Submit

/-!
# `Consensus.BeaconApi.Publish`

What a beacon node answers to a block or a payload envelope that a client asks it to publish.

The client picks a level of checks that the object must pass before the node broadcasts it.

The [block endpoint] and the [envelope endpoint] give the levels and the three answers.

SOUNDNESS.md records how this module reads the points that the source leaves open.

[block endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/blocks/blocks.v2.yaml
[envelope endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/execution_payload/envelope_post.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The level of checks that an object must pass before the node broadcasts it. -/
inductive BroadcastValidation where
  /-- The gossip checks of its topic only, the default. -/
  | gossip
  /-- The gossip checks, then the checks of the object against the state before it. -/
  | consensus
  /-- The consensus checks, then a check that its block has no rival in the store. -/
  | consensusAndEquivocation
  deriving DecidableEq, Repr

/-- The answer to an object to publish.

A refused object carries the reason, and the node answers 400. -/
inductive PublishOutcome where
  /-- The node broadcast the object and integrated it: status 200. -/
  | integrated
  /-- The node broadcast the object but could not integrate it: status 202. -/
  | broadcastNotIntegrated
  /-- The object failed its level, and the node did not broadcast it: status 400. -/
  | refused (reason : String)
  deriving DecidableEq, Repr

/-- The status code of an answer. -/
def PublishOutcome.status : PublishOutcome → Nat
  -- The source: validated, broadcast and integrated.
  | .integrated => 200
  -- The source: broadcast, but not integrated, as it failed full validation.
  | .broadcastNotIntegrated => 202
  -- The source: invalid, or broadcast validation failed.
  | .refused _ => 400

/-- The execution layer of the consensus checks of a block: it gives no verdict on a payload.

It answers from the checks below, even for a layer that answers a payload request in its own way.
-/
def consensusEngine (engine : ExecutionEngine preset fork) :
    ExecutionEngine preset fork where
  -- The check of the block hash of the payload is kept.
  isValidBlockHash := engine.isValidBlockHash
  -- From Deneb, the check of the versioned hashes is kept.
  isValidVersionedHashes := engine.isValidVersionedHashes
  -- The source leaves out the transactions of the payload, so their execution always passes.
  notifyNewPayload _ _ _ := true
  -- Its answer: no empty transaction, and both checks above pass.
  verifyAndNotifyNewPayload :=
    verifyAndNotify engine.isValidBlockHash engine.isValidVersionedHashes fun _ _ _ => true

/-- Whether the store holds a rival of a block: another root with the same slot and proposer. -/
def hasRival (store : Store preset fork) (root : Root) (block : BeaconBlock preset fork) : Bool :=
  -- The source names an equivocation and does not define it.
  --
  -- EthLib's reading: a held block of another root, with the same slot and the same proposer.
  store.blocks.any fun other held =>
    other != root && held.slot == block.slot && held.proposerIndex == block.proposerIndex

/-- The reason of a failed check of the fork choice, if it failed. -/
def checkFailure (label : String) : Except ForkChoiceError Unit → Option String
  | .ok () => none
  -- The message of the code 400 is EthLib's.
  | .error _ => some s!"{label}: the fork choice rejects it"

/-- The reason that an object fails a level, if it fails. -/
def levelFailure (level : BroadcastValidation) (gossip : Option String)
    (consensus : Unit → Option String) (rival : Unit → Bool) : Option String :=
  match gossip with
  -- The gossip checks run at every level, since a success means that they passed.
  | some reason => some reason
  | none =>
    match level with
    -- The source: gossip, the default, runs the gossip checks only.
    | .gossip => none
    -- The source: consensus adds the full consensus checks, with every signature.
    | .consensus => consensus ()
    -- The source: consensus and equivocation adds an equivocation check after those.
    --
    -- Each check runs only when those before it pass.
    | .consensusAndEquivocation =>
      match consensus () with
      | some reason => some reason
      | none => if rival () then some "equivocation: the block has a rival" else none

/-- The answer to an object to publish, the store after it and the messages seen after it.

A refused object leaves the store and the messages seen as they were. -/
def publish (context : SubmitContext preset fork) (seen : Seen) (level : BroadcastValidation)
    (message : GossipMessage preset fork) (consensus : Unit → Option String)
    (rival : Unit → Bool) (integrate : Unit → Except ForkChoiceError (Store preset fork)) :
    PublishOutcome × Store preset fork × Seen :=
  -- The gossip checks of the topic of the object, with the messages seen after them.
  let (gossip, broadcast) := messageFailure context seen message
  -- Then the later checks of the level.
  match levelFailure level gossip consensus rival with
  -- The source: an object that fails its level gets code 400 and is not broadcast.
  | some reason => (.refused reason, context.store, seen)
  -- Otherwise the node broadcasts it, so the keys of its message are seen.
  | none =>
    -- Then the node integrates it into the fork choice store: code 200, or 202 if it fails to.
    match integrate () with
    | .ok store => (.integrated, store, broadcast)
    | .error _ => (.broadcastNotIntegrated, context.store, broadcast)

/-- The consensus checks of a block: the transition from the state after its parent. -/
def blockConsensus (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) : Except ForkChoiceError Unit := do
  -- The state after the parent of the block.
  let state ← context.store.blockState signed.message.parentRoot
  -- The source: every signature and every field of the block, except the payload transactions.
  --
  -- The transition checks the signatures, the fields and the state root of the block.
  --
  -- Its execution layer gives no verdict on the payload, whose transactions the source leaves out.
  discard <| (stateTransition context.config context.checks (consensusEngine sources.engine)
    state signed true).mapError .transition

/-- Whether the store holds a rival of a block, which then fails the highest level. -/
def blockHasRival (store : Store preset fork) (block : BeaconBlock preset fork) : Bool :=
  match SszType.hashTreeRoot block with
  | .ok root => hasRival store root block
  -- A block whose root cannot be computed has no rival.
  | .error _ => false

/-- The answer to a block to publish, the store after it and the messages seen after it. -/
def publishBlock (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (seen : Seen) (level : BroadcastValidation) (signed : SignedBeaconBlock preset fork) :
    PublishOutcome × Store preset fork × Seen :=
  -- The gossip message of the block on its topic.
  publish context seen level (.beaconBlock signed)
    (fun _ => checkFailure "consensus" (blockConsensus context sources signed))
    (fun _ => blockHasRival context.store signed.message)
    -- A block that passes its level joins the store by the block handler of the fork choice.
    (fun _ => context.store.onBlock context.config context.checks sources signed)

/-- From Gloas: the consensus checks of an envelope, against the state after its block. -/
def envelopeConsensus (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ForkChoiceError Unit := do
  -- The state after the block that the envelope names.
  let state ← context.store.blockState signed.message.beaconBlockRoot
  -- The source: every signature and every field of the envelope.
  --
  -- They are checked against that state and the bid of the block.
  --
  -- The execution layer gives its verdict on the payload.
  --
  -- Unlike the block level, the envelope level of the source makes no exception for transactions.
  (verifyExecutionPayloadEnvelope context.config context.checks sources.engine state gloas
    signed).mapError .transition

/-- Whether the block that an envelope names has a rival in the store. -/
def envelopeHasRival (store : Store preset fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Bool :=
  -- The source: the beacon block of the envelope is not an equivocation.
  let root := signed.message.beaconBlockRoot
  match store.blocks[root]? with
  | some block => hasRival store root block
  -- An envelope whose block the store does not hold has no rival.
  | none => false

/-- From Gloas: the answer to an envelope to publish, the store and the messages seen after it. -/
def publishEnvelope (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (seen : Seen) (level : BroadcastValidation) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) :
    PublishOutcome × Store preset fork × Seen :=
  -- The gossip message of the envelope on its topic.
  publish context seen level (.executionPayloadEnvelope gloas signed)
    (fun _ => checkFailure "consensus" (envelopeConsensus context sources gloas signed))
    (fun _ => envelopeHasRival context.store signed)
    -- An envelope that passes its level joins the store by the envelope handler of the fork choice.
    (fun _ =>
      context.store.onExecutionPayloadEnvelope context.config context.checks sources gloas signed)

end EthLib.Consensus.BeaconApi
