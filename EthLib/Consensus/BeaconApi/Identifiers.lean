module

public import EthLib.Consensus.BeaconApi.Encoding
public import EthLib.Serialization.Ssz.Codec.HexBytes
public import EthLib.Consensus.ForkChoice.OptimisticSync

/-!
# `Consensus.BeaconApi.Identifiers`

The identifiers that name a state, a block or a validator in a path of the Beacon API.

Each identifier is read from its text, and resolved against the store of the fork choice.

The finalized flag is read from the same store, and the optimistic flag from the optimistic store.

[`params/index.yaml`] defines the state and block identifiers.

[`validator.yaml`] defines the validator identifier.

[`types/primitive.yaml`] defines the two flags.

SOUNDNESS.md records how this module reads the points that the source leaves open.

[`params/index.yaml`]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/params/index.yaml
[`validator.yaml`]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/validator.yaml
[`types/primitive.yaml`]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/primitive.yaml
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

/-- The number below 2^64 that a text writes in plain decimal, or none. -/
def parseUInt64 (text : String) : Option UInt64 :=
  -- The source names a slot or an index without fixing its text.
  --
  -- EthLib's choice: plain decimal, with no sign and no leading zero.
  match readNat (.str text) with
  -- A slot and an index are 64-bit numbers.
  | .ok n => if n < UInt64.size then some (UInt64.ofNat n) else none
  | .error _ => none

/-- The error of a text that names nothing, with code 400. -/
def invalidId (kind text : String) : ErrorMessage :=
  -- The source has the example Invalid state ID: current, and the other kinds follow it.
  { code := 400, message := s!"Invalid {kind} ID: {text}" }

/-- The state identifier that a text writes, or an error with code 400. -/
def parseStateId (text : String) : Except ErrorMessage StateId :=
  -- `params/index.yaml`: one of the words head, genesis, finalized and justified.
  if text = "head" then .ok .head
  else if text = "genesis" then .ok .genesis
  else if text = "finalized" then .ok .finalized
  else if text = "justified" then .ok .justified
  -- Else a slot.
  else match parseUInt64 text with
    | some slot => .ok (.slot slot)
    -- Else a state root: 32 bytes, hex encoded with the 0x prefix.
    | none => match parseHexBytes 32 text with
      | some root => .ok (.root root)
      -- Else an invalid state identifier: code 400.
      | none => .error (invalidId "state" text)

/-- The block identifier that a text writes, or an error with code 400. -/
def parseBlockId (text : String) : Except ErrorMessage BlockId :=
  -- `params/index.yaml`: one of the words head, genesis and finalized, with no justified block.
  if text = "head" then .ok .head
  else if text = "genesis" then .ok .genesis
  else if text = "finalized" then .ok .finalized
  -- Else a slot.
  else match parseUInt64 text with
    | some slot => .ok (.slot slot)
    -- Else a block root: 32 bytes, hex encoded with the 0x prefix.
    | none => match parseHexBytes 32 text with
      | some root => .ok (.root root)
      -- Else an invalid block identifier: code 400.
      | none => .error (invalidId "block" text)

/-- The validator identifier that a text writes, or an error with code 400. -/
def parseValidatorId (text : String) : Except ErrorMessage ValidatorId :=
  -- The validator endpoint and the lists of identifiers: a validator index.
  match parseUInt64 text with
  | some index => .ok (.index index)
  -- Else a public key: any 48 bytes, hex encoded with the 0x prefix.
  | none => match parseHexBytes 48 text with
    | some pubkey => .ok (.pubkey pubkey)
    -- Else an invalid validator identifier: code 400.
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
  -- The source: the canonical head in the node's view, here the head of the fork choice.
  (store.getHead config).toOption.map (·.root)

/-- The root of the block at a slot on the chain of a block, or none. -/
def blockAtSlot (store : Store preset fork) (start : Root) (slot : Slot) : Option Root := do
  -- The latest ancestor of the block at or below the slot.
  let node ← (store.getAncestor ⟨start, .pending⟩ slot).toOption
  let block ← store.blocks[node.root]?
  -- It must be at the slot itself, so a slot with no block names none.
  if block.slot = slot then some node.root else none

/-- The root of the block that an identifier names in the store, or none. -/
def resolveBlockId (config : Config) (store : Store preset fork) : BlockId → Option Root
  -- The canonical head in the node's view.
  | .head => headRoot config store
  -- EthLib's choice: the block of slot 0 on the chain of the head.
  | .genesis => (headRoot config store).bind fun head => blockAtSlot store head GENESIS_SLOT
  -- The block of the finalized checkpoint, as the store records it.
  | .finalized => some store.finalizedCheckpoint.root
  -- EthLib's choice: the block at the slot on the chain of the head.
  | .slot slot => (headRoot config store).bind fun head => blockAtSlot store head slot
  -- A root names a block only when the store holds it.
  | .root root => if store.blocks.contains root then some root else none

/-- The root of the block whose state root field is the given root, the first in the order of roots.

The store checks that the state after each of its blocks has the root that the block gives. -/
def blockOfStateRoot (store : Store preset fork) (stateRoot : Root) : Option Root :=
  -- The first block, in the order of roots, whose state root field is the root.
  (store.blocks.toList.find? fun (_, block) => block.stateRoot = stateRoot).map (·.1)

/-- The root of a block and the state after it, when the store holds that state. -/
def stateAfter (store : Store preset fork) (root : Root) :
    Option (Root × BeaconState preset fork) :=
  store.blockStates[root]?.map (root, ·)

/-- The state that an identifier names in the store, with the root of the block it follows. -/
def resolveStateId (config : Config) (store : Store preset fork) :
    StateId → Option (Root × BeaconState preset fork)
  -- A word names the state after the block that the same block identifier names.
  | .head => (resolveBlockId config store .head).bind (stateAfter store)
  | .genesis => (resolveBlockId config store .genesis).bind (stateAfter store)
  -- EthLib's choice: the state after the checkpoint block, not the checkpoint state.
  | .finalized => (resolveBlockId config store .finalized).bind (stateAfter store)
  -- EthLib's choice: the state after the block of the justified checkpoint, as for finalized.
  | .justified => stateAfter store store.justifiedCheckpoint.root
  -- EthLib's choice: the state after the block at the slot, so a slot with no block names none.
  | .slot slot => (resolveBlockId config store (.slot slot)).bind (stateAfter store)
  -- EthLib's choice: the state after the first block whose state root field is the root.
  --
  -- So the root of a state after empty slots names none.
  | .root root => (blockOfStateRoot store root).bind (stateAfter store)

/-- The index of the validator that an identifier names in a state, or none. -/
def resolveValidatorId (state : BeaconState preset fork) : ValidatorId → Option ValidatorIndex
  -- An index names a validator when it is below the size of the registry.
  | .index index => if index.toNat < state.validators.data.size then some index else none
  -- A public key names the first validator of the registry that holds it, EthLib's choice.
  --
  -- The source does not say which validator a key held twice names.
  | .pubkey pubkey => (state.validators.data.findIdx? (·.pubkey == pubkey)).map UInt64.ofNat

/-- Whether a block is the block of the finalized checkpoint or one of its ancestors.

The source asks whether a response references the finalized history of the chain. -/
def isFinalizedRoot (store : Store preset fork) (root : Root) : Bool :=
  match store.blocks[root]? with
  -- A block that the store does not hold is not reported finalized.
  | none => false
  | some block =>
    -- The ancestor of the finalized block at the slot of the block is the block itself.
    match store.getAncestor ⟨store.finalizedCheckpoint.root, .pending⟩ block.slot with
    | .ok node => node.root == root
    -- A block with no such ancestor is not reported finalized.
    | .error _ => false

/-- Whether a response that references a block references a payload not yet verified. -/
def isExecutionOptimistic (optimistic : OptimisticStore preset fork) (root : Root) : Bool :=
  -- The source: true if the response references an unverified execution payload.
  optimistic.isOptimistic root

end EthLib.Consensus.BeaconApi
