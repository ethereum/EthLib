module

public import EthLib.Consensus.BeaconApi.Encoding
public import EthLib.Consensus.ForkChoice.OptimisticSync

/-!
# `Consensus.BeaconApi.Identifiers`

The identifiers that name a state, a block or a validator in a path of the Beacon API.

Each identifier is read from its text, and resolved against the store of the fork choice.

The finalized flag is read from the same store, and the optimistic flag from the optimistic store.

[`params/index.yaml`] defines the state and block identifiers.

[`validator.yaml`] defines the validator identifier.

[`types/primitive.yaml`] defines the two flags.

A text that is no identifier gives an error with code 400.

SOUNDNESS.md records how this module reads the points that the source leaves open.

[`params/index.yaml`]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/params/index.yaml
[`validator.yaml`]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/validator.yaml
[`types/primitive.yaml`]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/primitive.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Serialization.Ssz Cryptography.Bls

/-- The name of a state in a path: a word, a slot, or the root of the state. -/
inductive StateId where
  /-- The state after the head of the fork choice. -/
  | head
  /-- The state after the block of slot 0 on the chain of the head. -/
  | genesis
  /-- The state after the block of the finalized checkpoint. -/
  | finalized
  /-- The state after the block of the justified checkpoint. -/
  | justified
  /-- The state after the block of a slot on the chain of the head. -/
  | slot (slot : Slot)
  /-- The state whose root is given. -/
  | root (root : Root)
  deriving DecidableEq, Repr

/-- The name of a block in a path: a word, a slot, or the root of the block. -/
inductive BlockId where
  /-- The head of the fork choice. -/
  | head
  /-- The block of slot 0 on the chain of the head. -/
  | genesis
  /-- The block of the finalized checkpoint. -/
  | finalized
  /-- The block of a slot on the chain of the head. -/
  | slot (slot : Slot)
  /-- The block whose root is given. -/
  | root (root : Root)
  deriving DecidableEq, Repr

/-- The name of a validator in a path: its index, or its public key. -/
inductive ValidatorId where
  /-- The validator at an index of the registry. -/
  | index (index : ValidatorIndex)
  /-- The first validator of the registry whose public key is the given one. -/
  | pubkey (pubkey : BLSPubkey)
  deriving DecidableEq, Repr

/-- The number below 2⁶⁴ that a text writes in plain decimal, or none. -/
def parseUInt64 (text : String) : Option UInt64 :=
  match readNat (.str text) with
  | .ok n => if n < UInt64.size then some (UInt64.ofNat n) else none
  | .error _ => none

/-- The bytes of a given count that a text writes as hex after a lowercase `0x`, or none.

The digits may be in either case. -/
def parseHexBytes (count : Nat) (text : String) : Option (Vector UInt8 count) :=
  match ofHex text with
  | .ok data => if size : data.size = count then some ⟨data, size⟩ else none
  | .error _ => none

/-- The error of a text that names nothing, with code 400. -/
def invalidId (kind text : String) : ErrorMessage :=
  { code := 400, message := s!"Invalid {kind} ID: {text}" }

/-- The state identifier that a text writes, or an error with code 400. -/
def parseStateId (text : String) : Except ErrorMessage StateId :=
  if text = "head" then .ok .head
  else if text = "genesis" then .ok .genesis
  else if text = "finalized" then .ok .finalized
  else if text = "justified" then .ok .justified
  else match parseUInt64 text with
    | some slot => .ok (.slot slot)
    | none => match parseHexBytes 32 text with
      | some root => .ok (.root root)
      | none => .error (invalidId "state" text)

/-- The block identifier that a text writes, or an error with code 400. -/
def parseBlockId (text : String) : Except ErrorMessage BlockId :=
  if text = "head" then .ok .head
  else if text = "genesis" then .ok .genesis
  else if text = "finalized" then .ok .finalized
  else match parseUInt64 text with
    | some slot => .ok (.slot slot)
    | none => match parseHexBytes 32 text with
      | some root => .ok (.root root)
      | none => .error (invalidId "block" text)

/-- The validator identifier that a text writes, or an error with code 400. -/
def parseValidatorId (text : String) : Except ErrorMessage ValidatorId :=
  match parseUInt64 text with
  | some index => .ok (.index index)
  | none => match parseHexBytes 48 text with
    | some pubkey => .ok (.pubkey pubkey)
    | none => .error (invalidId "validator" text)

/-- The text of a state identifier, with lowercase hex. -/
def printStateId : StateId → String
  | .head => "head"
  | .genesis => "genesis"
  | .finalized => "finalized"
  | .justified => "justified"
  | .slot slot => toString slot.toNat
  | .root root => toHex root.toArray

/-- The text of a block identifier, with lowercase hex. -/
def printBlockId : BlockId → String
  | .head => "head"
  | .genesis => "genesis"
  | .finalized => "finalized"
  | .slot slot => toString slot.toNat
  | .root root => toHex root.toArray

/-- The text of a validator identifier, with lowercase hex. -/
def printValidatorId : ValidatorId → String
  | .index index => toString index.toNat
  | .pubkey pubkey => toHex pubkey.toArray

variable {preset : Preset} {fork : Base.Fork}

/-- The root of the head of the fork choice, or none when the head cannot be computed. -/
def headRoot (config : Config) (store : Store preset fork) : Option Root :=
  (store.getHead config).toOption.map (·.root)

/-- The root of the block at a slot on the chain of a block, or none.

The walk takes the latest ancestor at or below the slot, which must be at the slot itself. -/
def blockAtSlot (store : Store preset fork) (start : Root) (slot : Slot) : Option Root := do
  let node ← (store.getAncestor ⟨start, .pending⟩ slot).toOption
  let block ← store.blocks[node.root]?
  if block.slot = slot then some node.root else none

/-- The root of the block that an identifier names in the store, or none.

A root names a block only when the store holds it.

The finalized checkpoint names its root as the store records it. -/
def resolveBlockId (config : Config) (store : Store preset fork) : BlockId → Option Root
  | .head => headRoot config store
  | .genesis => (headRoot config store).bind fun head => blockAtSlot store head GENESIS_SLOT
  | .finalized => some store.finalizedCheckpoint.root
  | .slot slot => (headRoot config store).bind fun head => blockAtSlot store head slot
  | .root root => if store.blocks.contains root then some root else none

/-- The root of the block whose state root field is the given root, the first in the order of roots.

The store checks that the state after each of its blocks has the root that the block gives. -/
def blockOfStateRoot (store : Store preset fork) (stateRoot : Root) : Option Root :=
  (store.blocks.toList.find? fun (_, block) => block.stateRoot = stateRoot).map (·.1)

/-- The root of a block and the state after it, when the store holds that state. -/
def stateAfter (store : Store preset fork) (root : Root) :
    Option (Root × BeaconState preset fork) :=
  store.blockStates[root]?.map (root, ·)

/-- The state that an identifier names in the store, with the root of the block it follows. -/
def resolveStateId (config : Config) (store : Store preset fork) :
    StateId → Option (Root × BeaconState preset fork)
  | .head => (resolveBlockId config store .head).bind (stateAfter store)
  | .genesis => (resolveBlockId config store .genesis).bind (stateAfter store)
  | .finalized => (resolveBlockId config store .finalized).bind (stateAfter store)
  | .justified => stateAfter store store.justifiedCheckpoint.root
  | .slot slot => (resolveBlockId config store (.slot slot)).bind (stateAfter store)
  | .root root => (blockOfStateRoot store root).bind (stateAfter store)

/-- The index of the validator that an identifier names in a state, or none.

An index names a validator when it is below the size of the registry. -/
def resolveValidatorId (state : BeaconState preset fork) : ValidatorId → Option ValidatorIndex
  | .index index => if index.toNat < state.validators.data.size then some index else none
  | .pubkey pubkey => (state.validators.data.findIdx? (·.pubkey == pubkey)).map UInt64.ofNat

/-- Whether a block is the block of the finalized checkpoint or one of its ancestors.

The ancestor of the finalized block at the slot of the block must be the block itself. -/
def isFinalizedRoot (store : Store preset fork) (root : Root) : Bool :=
  match store.blocks[root]? with
  | none => false
  | some block =>
    match store.getAncestor ⟨store.finalizedCheckpoint.root, .pending⟩ block.slot with
    | .ok node => node.root == root
    | .error _ => false

/-- Whether a response that references a block references a payload not yet verified. -/
def isExecutionOptimistic (optimistic : OptimisticStore preset fork) (root : Root) : Bool :=
  optimistic.isOptimistic root

end EthLib.Consensus.BeaconApi
