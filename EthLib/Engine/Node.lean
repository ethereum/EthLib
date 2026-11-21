module

public import EthLib.Engine.GetPayload

/-!
# `Engine.Node`

An execution node that keeps what the Engine API tells it, from one call to the next.

It knows blocks by hash, each with its header and its validity.

A valid block also has the state after it, so a payload on it can run.

The node also keeps the forkchoice state of the last update that applied a head.

It also has a store of completed builds, by payload ID, which no step fills yet.

Each method is a step: the node and the request give an answer and the next node.

Each step answers with the rule of its method, on a view of the node.

A payload runs on the chain that ends at its parent, with the state after that parent.

A forkchoice update reads the tree of the known blocks and the known finalized block.

A request for a payload reads the builds.

A payload that the node already knows gets that status again.

A payload whose parent is the head runs at once.

A payload on another known parent that is not invalid is accepted, and kept without running.

An update validates the accepted blocks of the chain of its head, oldest first, before its rules.

A block on a parent found invalid is invalid too.

A head that is still accepted then, since a run aborted, is syncing.

A payload that fails the checks before execution leaves the node as it was.

Those checks read the other parameters of the request too, so they say nothing of the block alone.

An update applies its forkchoice state whenever it applies its head.

Step 8 of the update keeps that state even when the checks of its payload attributes then fail.

The node keeps the state after every valid block, so it takes a reorganization of any depth.

The source lets a node refuse a deep one with `-38006`, and this node never does.

The sources are at commit `3284ee8` of execution-apis.

They are the [payload validation][validation] of Paris, and three of its methods:

- [`engine_newPayloadV1`][new]
- [`engine_forkchoiceUpdatedV1`][fcu]
- [`engine_getPayloadV1`][get]

[validation]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-validation
[new]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_newpayloadv1
[fcu]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_forkchoiceupdatedv1
[get]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_getpayloadv1
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Blocks (BlockChain RecentBlock)

/-- What a node knows of the validity of a block. -/
inductive Validity where
  /-- The block and its ancestors are valid, and this is the state after the block. -/
  | valid (post : Execution.State.State)
  /-- The block or one of its ancestors is invalid. -/
  | invalid
  /-- The block arrived off the head and has not run: the request is kept, to run it later. -/
  | accepted (version : Nat) (params : Json)

/-- Whether a validity is that of a valid block. -/
def Validity.isValid : Validity → Bool
  | .valid _ => true
  | _ => false

/-- Whether a validity is that of an accepted block, which has not run. -/
def Validity.isAccepted : Validity → Bool
  | .accepted _ _ => true
  | _ => false

/-- A block that a node knows: its header at its fork, its validity and its proof of work totals. -/
structure KnownBlock where
  /-- The block, at its fork, with its header and its ommers. -/
  block : RecentBlock
  /-- For a block of proof of work, its total difficulty and its parent's; `none` otherwise. -/
  powTotalDifficulty : Option (Nat × Nat)
  /-- What the node knows of its validity. -/
  validity : Validity

/-- A known block as the forkchoice update reads it: its parent, validity, number and time. -/
def KnownBlock.toKnownPayload (b : KnownBlock) : KnownPayload :=
  ⟨b.block.header.parentHash, b.validity.isValid, UInt64.ofNat b.block.header.number,
    UInt64.ofNat b.block.header.timestamp.toNat, b.powTotalDifficulty⟩

/-- An execution node, as the Engine API sees it. -/
structure Node where
  /-- The configuration of the chain. -/
  config : ChainConfig
  /-- The configuration of the transition, with the terminal total difficulty. -/
  transition : TransitionConfiguration
  /-- The known blocks by hash, newest first; the first entry of a hash is the one that counts. -/
  blocks : List (Hash32 × KnownBlock)
  /-- The forkchoice state of the last update that applied a head. -/
  forkchoice : ForkchoiceState
  /-- The finalized block that the last such update named, unless that hash was zero. -/
  finalized : Option Hash32
  /-- The completed builds, by payload ID. -/
  builds : List (PayloadId × StoredPayload)

namespace Node

/-- A node that knows one block, valid with a state, as its head.

A block of proof of work also needs its total difficulty, at least its difficulty.

The total of its parent is then its own total minus its difficulty.

From Paris on, the total is not read.

The safe and finalized hashes are zero, and the node knows no finalized block.

There is no node when the header has no hash, or when a total is below the difficulty.

The forkchoice update reads the number and the time of the block in 64 bits. -/
def start (config : ChainConfig) (transition : TransitionConfiguration) (anchor : RecentBlock)
    (post : Execution.State.State) (totalDifficulty : Nat) : Option Node := do
  let hash ← anchor.header.hash.toOption
  let pow ← if anchor.fork < .paris then
      if anchor.header.difficulty ≤ totalDifficulty then
        some (some (totalDifficulty, totalDifficulty - anchor.header.difficulty))
      else none
    else some none
  return { config, transition, blocks := [(hash, ⟨anchor, pow, .valid post⟩)],
           forkchoice := ⟨hash, ZERO_HASH, ZERO_HASH⟩, finalized := none, builds := [] }

/-- The tree of the known blocks, as the forkchoice update reads it. -/
def tree (node : Node) : PayloadTree :=
  node.blocks.map fun (hash, b) => (hash, b.toKnownPayload)

/-- The builds, as the request for a payload reads them. -/
def store (node : Node) : PayloadStore :=
  fun id => node.builds.lookup id

/-- The state after a known valid block. -/
def validState (node : Node) (hash : Hash32) : Option Execution.State.State :=
  match node.blocks.lookup hash with
  | some ⟨_, _, .valid post⟩ => some post
  | _ => none

/-- The total difficulty of a known block of proof of work, and 0 for any other block. -/
def totalDifficulty (node : Node) (hash : Hash32) : Nat :=
  ((node.blocks.lookup hash).bind (·.powTotalDifficulty)).elim 0 (·.1)

/-- The known blocks of the chain that ends at a block, oldest first, at most 255 of them.

The block hashes that a block reads need only the last 255 blocks before it. -/
def recentTo (node : Node) (hash : Hash32) : List RecentBlock :=
  ((ancestors node.tree 255 hash).filterMap fun h => (node.blocks.lookup h).map (·.block)).reverse

/-- The chain that ends at a block, with a state after it. -/
def chainAt (node : Node) (hash : Hash32) (post : Execution.State.State) : BlockChain :=
  ⟨node.config, post, node.recentTo hash⟩

/-- The node that also knows a block; its entry comes first, so it is the one that counts. -/
def record (node : Node) (hash : Hash32) (b : KnownBlock) : Node :=
  { node with blocks := (hash, b) :: node.blocks }

/-- The node after the execution of a payload on its parent.

A valid payload is known as valid, with the state after it.

A payload invalid in execution is known as invalid.

So is a payload on a parent that fails the terminal block check.

A payload whose execution aborts stays unknown. -/
def recordExecution (node : Node) (hash : Hash32) (block : RecentBlock) (status : PayloadStatus)
    (next : Option (RecentBlock × Execution.State.State)) : Node :=
  match next with
  | some (_, post) => node.record hash ⟨block, none, .valid post⟩
  | none => if status.status = .invalid then node.record hash ⟨block, none, .invalid⟩ else node

/-- The answer of the method to a payload run on its known valid parent, and the next node.

The payload runs on the chain that ends at that parent, with the state after it.

The node then records the payload, unless its execution aborts. -/
def executeOn (node : Node) (hash : Hash32) (block : RecentBlock) (post : Execution.State.State)
    (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) × Node :=
  let parent := block.header.parentHash
  match newPayloadOnChain node.transition (node.totalDifficulty parent)
      (node.chainAt parent post) version params with
  | .error e => (.error e, node)
  | .ok (status, reason, next) =>
    (.ok (status, reason), node.recordExecution hash block status next)

/-- The answer to a payload that the node does not know as valid or invalid, by its parent.

A payload whose parent is the valid head runs on the chain of that parent.

A payload on another known parent that is not invalid is accepted, with no latest valid hash.

The node keeps it as accepted, with its request, as step 5 of the method allows.

A payload whose parent is invalid is invalid too, since each ancestor must pass validation.

Step 1 of payload validation asks this, as the block validity of EIP-3675 does.

Its latest valid hash is the latest valid block of the chain of its parent.

That hash is zero when that block is of proof of work, by step 3 of payload validation.

The node keeps it as invalid.

A payload whose parent is unknown is syncing. -/
def onParent (node : Node) (hash : Hash32) (block : RecentBlock) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) × Node :=
  let accept : Except EngineError (PayloadStatus × Option PayloadError) × Node :=
    (.ok (⟨.accepted, none⟩, none), node.record hash ⟨block, none, .accepted version params⟩)
  let parent := block.header.parentHash
  match node.blocks.lookup parent with
  | some ⟨_, _, .valid post⟩ =>
    if parent = node.forkchoice.headBlockHash then node.executeOn hash block post version params
    else accept
  | some ⟨_, _, .accepted _ _⟩ => accept
  | some ⟨_, _, .invalid⟩ =>
    (.ok (⟨.invalid, latestValidHash node.tree parent⟩, none),
      node.record hash ⟨block, none, .invalid⟩)
  | none => (.ok (⟨.syncing, none⟩, none), node)

/-- The step of `engine_newPayload`: the status of a payload, with its reason, and the next node.

The checks before execution run first, and a payload that fails them leaves the node as it was.

A known valid payload is valid, with its own hash as the latest valid hash.

A known invalid payload is invalid, with the latest valid block of its chain.

Any other payload gets the answer that its parent gives, even one that the node keeps as accepted.
-/
def newPayloadStep (node : Node) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) × Node :=
  match checkNewPayload node.config version params with
  | .error e => (.error e, node)
  | .ok (.error (status, reason)) => (.ok (status, some reason), node)
  | .ok (.ok checked) =>
    let header := checked.block.header
    -- The checks give a block whose hash is the block hash of the payload, so this always holds.
    match header.hash with
    | .error _ => (.ok (⟨.syncing, none⟩, none), node)
    | .ok hash =>
      match node.blocks.lookup hash with
      | some ⟨_, _, .valid _⟩ => (.ok (⟨.valid, some hash⟩, none), node)
      | some ⟨_, _, .invalid⟩ => (.ok (⟨.invalid, latestValidHash node.tree hash⟩, none), node)
      | _ => node.onParent hash ⟨checked.fork, header, []⟩ version params

/-- The node after it validates the accepted blocks of the chain that ends at a block.

The blocks run oldest first, each on its parent once that parent is valid.

A block whose parent is then invalid is invalid too, by step 1 of payload validation.

A block whose parent is not known as valid or invalid stays accepted, as does one whose run aborts.

The fuel bounds the number of blocks, and the update gives the number of known blocks. -/
def validateChain (node : Node) : Nat → Hash32 → Node
  | 0, _ => node
  | fuel + 1, hash =>
    match node.blocks.lookup hash with
    | some ⟨block, _, .accepted version params⟩ =>
      let node := node.validateChain fuel block.header.parentHash
      match node.blocks.lookup block.header.parentHash with
      | some ⟨_, _, .valid post⟩ => (node.executeOn hash block post version params).2
      | some ⟨_, _, .invalid⟩ => node.record hash ⟨block, none, .invalid⟩
      | _ => node
    | _ => node

/-- The node after an update validates the chain of the head that it names.

Parameters that do not decode validate nothing. -/
def validateHead (node : Node) (version : Nat) (params : Json) : Node :=
  match forkchoiceUpdatedParams version params with
  | .ok (state, _) => node.validateChain node.blocks.length state.headBlockHash
  | .error _ => node

/-- Whether an update names a head that the node knows as accepted, which it could not validate. -/
def headAccepted (node : Node) (version : Nat) (params : Json) : Bool :=
  match forkchoiceUpdatedParams version params with
  | .ok (state, _) => (node.blocks.lookup state.headBlockHash).any (·.validity.isAccepted)
  | .error _ => false

/-- The node after an update applies a forkchoice state.

The state becomes that of the node.

A finalized hash that is not zero becomes the known finalized block. -/
def applyForkchoice (node : Node) (state : ForkchoiceState) : Node :=
  { node with
    forkchoice := state
    finalized := if state.finalizedBlockHash = ZERO_HASH then node.finalized
      else some state.finalizedBlockHash }

/-- The forkchoice state that an update applies, if it applies its head. -/
def appliedState (node : Node) (version : Nat) (params : Json) : Option ForkchoiceState :=
  match forkchoiceUpdatedParams version params with
  | .ok (state, _) =>
    match Engine.forkchoiceUpdated node.transition node.tree node.finalized state with
    | .ok (_, some _) => some state
    | _ => none
  | .error _ => none

/-- An update on a node whose head is validated: the response, and the next node.

The response is that of the method on the tree of the known blocks and the known finalized block.

The node applies the forkchoice state when the update applies its head, whatever the attributes. -/
def updateStep (node : Node) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadId) × Node :=
  let answer := forkchoiceUpdatedCall node.config node.transition version node.tree node.finalized
    params
  let next := match node.appliedState version params with
    | some state => node.applyForkchoice state
    | none => node
  (forkchoiceUpdatedResponse <$> answer, next)

/-- The step of `engine_forkchoiceUpdated`: the response, and the next node.

The node first validates the accepted blocks of the chain of the head, by step 4 of the method.

A head that is still accepted is syncing, and the update applies nothing.

Otherwise the update runs on the validated node. -/
def forkchoiceUpdatedStep (node : Node) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadId) × Node :=
  let node := node.validateHead version params
  if node.headAccepted version params then (.ok (⟨.syncing, none⟩, none), node)
  else node.updateStep version params

/-- The step of `engine_getPayload`: the build of a payload ID, and the node as it was.

The trusted setup checks the proofs of the blobs, from version 3. -/
def getPayloadStep (node : Node) (setup : TrustedSetup) (version : Nat) (id : PayloadId) :
    Except GetPayloadError GetPayloadResponse × Node :=
  (getPayload node.config setup node.store version id, node)

end Node

end EthLib.Engine
