module

public import EthLib.Consensus.BeaconApi.Submit

/-!
# `Consensus.BeaconApi.Publish`

What a beacon node answers to a block or a payload envelope that a client asks it to publish.

The client picks a level of checks that the object must pass before the node broadcasts it.

The gossip checks of its topic run at every level, since a success means that they passed.

The consensus level adds the checks of the object, with its signatures, against the state before.

For a block, the execution layer checks the hashes of a payload and its empty transactions.

It gives no verdict on the payload itself.

For an envelope, it gives its verdict too.

The highest level also refuses an object whose block has a rival in the store.

A rival is another block of the same slot and the same proposer.

An object that fails its level is refused and not broadcast, and the node keeps its state.

Otherwise the node broadcasts it, then integrates it into the fork choice store, or fails to.

The [block endpoint] and the [envelope endpoint] give the levels and the three answers.

SOUNDNESS.md records how this module reads the points that the source leaves open.

[block endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/blocks/blocks.v2.yaml
[envelope endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/execution_payload/envelope_post.yaml
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
  | .integrated => 200
  | .broadcastNotIntegrated => 202
  | .refused _ => 400

/-- The execution layer of the consensus checks of a block: it gives no verdict on a payload.

It keeps the checks of the hash and of the versioned hashes, and refuses an empty transaction.

It answers from these checks, even for a layer that answers in its own way. -/
def consensusEngine (engine : ExecutionEngine preset fork) :
    ExecutionEngine preset fork where
  isValidBlockHash := engine.isValidBlockHash
  isValidVersionedHashes := engine.isValidVersionedHashes
  notifyNewPayload _ _ _ := true
  verifyAndNotifyNewPayload :=
    verifyAndNotify engine.isValidBlockHash engine.isValidVersionedHashes fun _ _ _ => true

/-- Whether the store holds a rival of a block: another root with the same slot and proposer. -/
def hasRival (store : Store preset fork) (root : Root) (block : BeaconBlock preset fork) : Bool :=
  store.blocks.any fun other held =>
    other != root && held.slot == block.slot && held.proposerIndex == block.proposerIndex

/-- The reason of a failed check of the fork choice, if it failed. -/
def checkFailure (label : String) : Except ForkChoiceError Unit → Option String
  | .ok () => none
  | .error _ => some s!"{label}: the fork choice rejects it"

/-- The reason that an object fails a level, if it fails.

A failure of its gossip checks comes first, and each later check runs only when those before pass.
-/
def levelFailure (level : BroadcastValidation) (gossip : Option String)
    (consensus : Unit → Option String) (rival : Unit → Bool) : Option String :=
  match gossip with
  | some reason => some reason
  | none =>
    match level with
    | .gossip => none
    | .consensus => consensus ()
    | .consensusAndEquivocation =>
      match consensus () with
      | some reason => some reason
      | none => if rival () then some "equivocation: the block has a rival" else none

/-- The answer to an object to publish, the store after it and the messages seen after it.

The node checks the gossip message of the object, then the later checks of the level.

A refused object leaves the store and the messages seen as they were.

Otherwise the keys of the message are seen, and the node integrates the object if it can. -/
def publish (context : SubmitContext preset fork) (seen : Seen) (level : BroadcastValidation)
    (message : GossipMessage preset fork) (consensus : Unit → Option String)
    (rival : Unit → Bool) (integrate : Unit → Except ForkChoiceError (Store preset fork)) :
    PublishOutcome × Store preset fork × Seen :=
  let (gossip, broadcast) := messageFailure context seen message
  match levelFailure level gossip consensus rival with
  | some reason => (.refused reason, context.store, seen)
  | none =>
    match integrate () with
    | .ok store => (.integrated, store, broadcast)
    | .error _ => (.broadcastNotIntegrated, context.store, broadcast)

/-- The consensus checks of a block: the transition from the state after its parent.

The transition checks the signatures, the fields and the state root of the block.

The execution layer gives no verdict on its payload, since the source leaves out its transactions.
-/
def blockConsensus (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) : Except ForkChoiceError Unit := do
  let state ← context.store.blockState signed.message.parentRoot
  discard <| (stateTransition context.config context.checks (consensusEngine sources.engine)
    state signed true).mapError .transition

/-- Whether the store holds a rival of a block, which then fails the highest level.

A block whose root cannot be computed has no rival. -/
def blockHasRival (store : Store preset fork) (block : BeaconBlock preset fork) : Bool :=
  match SszType.hashTreeRoot block with
  | .ok root => hasRival store root block
  | .error _ => false

/-- The answer to a block to publish, the store after it and the messages seen after it.

A block that passes its level joins the store by the block handler of the fork choice. -/
def publishBlock (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (seen : Seen) (level : BroadcastValidation) (signed : SignedBeaconBlock preset fork) :
    PublishOutcome × Store preset fork × Seen :=
  publish context seen level (.beaconBlock signed)
    (fun _ => checkFailure "consensus" (blockConsensus context sources signed))
    (fun _ => blockHasRival context.store signed.message)
    (fun _ => context.store.onBlock context.config context.checks sources signed)

/-- From Gloas: the consensus checks of an envelope, against the state after its block.

They check its signature and its fields against that state and the bid of the block.

The execution layer gives its verdict on the payload. -/
def envelopeConsensus (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ForkChoiceError Unit := do
  let state ← context.store.blockState signed.message.beaconBlockRoot
  (verifyExecutionPayloadEnvelope context.config context.checks sources.engine state gloas
    signed).mapError .transition

/-- Whether the block that an envelope names has a rival in the store.

An envelope whose block the store does not hold has no rival. -/
def envelopeHasRival (store : Store preset fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) : Bool :=
  let root := signed.message.beaconBlockRoot
  match store.blocks[root]? with
  | some block => hasRival store root block
  | none => false

/-- From Gloas: the answer to an envelope to publish, the store and the messages seen after it.

An envelope that passes its level joins the store by the envelope handler of the fork choice. -/
def publishEnvelope (context : SubmitContext preset fork) (sources : BlockSources preset fork)
    (seen : Seen) (level : BroadcastValidation) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) :
    PublishOutcome × Store preset fork × Seen :=
  publish context seen level (.executionPayloadEnvelope gloas signed)
    (fun _ => checkFailure "consensus" (envelopeConsensus context sources gloas signed))
    (fun _ => envelopeHasRival context.store signed)
    (fun _ =>
      context.store.onExecutionPayloadEnvelope context.config context.checks sources gloas signed)

end EthLib.Consensus.BeaconApi
