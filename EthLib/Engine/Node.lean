module

public import EthLib.Engine.GetPayload

/-!
# `Engine.Node`

An execution node that keeps what the Engine API tells it, from one call to the next.

Each method is a step: the node and the request give an answer and the next node.

Each step answers with the rule of its method, on a view of the node.

A step comment names the method or the routine whose step it follows.

The sources are at commit `3284ee8` of execution-apis.

They are the [payload validation][validation] of Paris, and three of its methods:

- [`engine_newPayloadV1`][new]
- [`engine_forkchoiceUpdatedV1`][fcu]
- [`engine_getPayloadV1`][get]

The builds follow the [payload building][building] of Paris.

[validation]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-validation
[new]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_newpayloadv1
[fcu]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_forkchoiceupdatedv1
[get]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_getpayloadv1
[building]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-building
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Blocks (Block BlockChain RecentBlock)
open EthLib.Execution.Transactions (Transaction)

/-- What a node knows of the validity of a block. -/
inductive Validity where
  -- The state after a valid block lets a payload on it run.
  /-- The block and its ancestors are valid, and this is the state after the block. -/
  | valid (post : Execution.State.State)
  /-- The block or one of its ancestors is invalid. -/
  | invalid
  -- `engine_newPayloadV1`, step 5: a payload off the canonical chain may stay unvalidated.
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

/-- A block that a node knows: the block at its fork, its validity and its proof of work totals. -/
structure KnownBlock where
  -- The node keeps the body, so the receipts of a block can be found again by running it.
  /-- The block at its fork: its header, its ommers, its transactions and its withdrawals. -/
  full : (fork : Fork) × Block fork Transaction
  /-- For a block of proof of work, its total difficulty and its parent's; `none` otherwise. -/
  powTotalDifficulty : Option (Nat × Nat)
  /-- What the node knows of its validity. -/
  validity : Validity

/-- A known block as a recent block of a chain: its fork, its header and its ommers. -/
def KnownBlock.block (b : KnownBlock) : RecentBlock :=
  ⟨b.full.1, b.full.2.header, b.full.2.ommers⟩

/-- A known block as the forkchoice update reads it: its parent, validity, number and time. -/
def KnownBlock.toKnownPayload (b : KnownBlock) : KnownPayload :=
  ⟨b.block.header.parentHash, b.validity.isValid, b.block.header.number,
    b.block.header.timestamp.toNat, b.powTotalDifficulty⟩

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

/-- Whether the header of a recent block commits to its ommers and to an empty body.

An empty body has no transaction and, from Shapella, no withdrawal. -/
def commitsToEmptyBody (b : RecentBlock) : Bool :=
  let withdrawals := if h : .shapella ≤ b.fork then some (b.header.withdrawalsRoot h) else none
  let ommers := (Serialization.Rlp.encode (Execution.Blocks.ommersItem b.ommers)).toOption
  (Execution.Blocks.transactionsRoot []).toOption == some b.header.transactionsRoot &&
    (Execution.Blocks.withdrawalsRootOf (fork := b.fork) fun _ => []).toOption ==
      some withdrawals &&
    ommers.map Cryptography.Hash.Keccak.keccak256 == some b.header.ommersHash

namespace Node

/-- A node that knows one block, valid with a state, as its head.

There is no node when the header has no hash, or commits to another body or other ommers.

There is none either when a total is below the difficulty. -/
def start (config : ChainConfig) (transition : TransitionConfiguration) (anchor : RecentBlock)
    (post : Execution.State.State) (totalDifficulty : Nat) : Option Node := do
  let hash ← anchor.header.hash.toOption
  -- The node keeps the block with an empty body, so its header must commit to it and its ommers.
  unless commitsToEmptyBody anchor do none
  let block : Block anchor.fork Transaction := ⟨anchor.header, [], anchor.ommers, fun _ => []⟩
  -- A block of proof of work also needs its total difficulty, at least its difficulty.
  --
  -- The total of its parent is then its own total minus its difficulty.
  --
  -- From Paris on, the total is not read.
  let pow ← if anchor.fork < .paris then
      if anchor.header.difficulty ≤ totalDifficulty then
        some (some (totalDifficulty, totalDifficulty - anchor.header.difficulty))
      else none
    else some none
  -- The safe and finalized hashes are zero, and the node knows no finalized block.
  return { config, transition, blocks := [(hash, ⟨⟨_, block⟩, pow, .valid post⟩)],
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

/-- The node after the execution of a payload on its parent. -/
def recordExecution (node : Node) (hash : Hash32) (block : (fork : Fork) × Block fork Transaction)
    (status : PayloadStatus) (next : Option (RecentBlock × Execution.State.State)) : Node :=
  match next with
  -- Payload validation, step 3: a valid payload is known as valid, with the state after it.
  | some (_, post) => node.record hash ⟨block, none, .valid post⟩
  -- Step 3: a payload invalid in execution is known as invalid.
  --
  -- Step 2: so is a payload on a parent that fails the terminal block check.
  --
  -- A payload whose execution aborts stays unknown.
  | none => if status.status = .invalid then node.record hash ⟨block, none, .invalid⟩ else node

/-- The answer of the method to a payload run on its known valid parent, and the next node. -/
def executeOn (node : Node) (hash : Hash32) (block : (fork : Fork) × Block fork Transaction)
    (post : Execution.State.State) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) × Node :=
  let parent := block.2.header.parentHash
  -- The payload runs on the chain that ends at its parent, with the state after that parent.
  match newPayloadOnChain node.transition (node.totalDifficulty parent)
      (node.chainAt parent post) version params with
  | .error e => (.error e, node)
  -- The node then records the payload, unless its execution aborts.
  | .ok (status, reason, next) =>
    (.ok (status, reason), node.recordExecution hash block status next)

/-- The answer to a payload that the node does not know as valid or invalid, by its parent. -/
def onParent (node : Node) (hash : Hash32) (block : (fork : Fork) × Block fork Transaction)
    (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) × Node :=
  -- `engine_newPayloadV1`, step 6: `ACCEPTED`, with no latest valid hash.
  --
  -- The node keeps the payload as accepted, with its request, as step 5 allows.
  let accept : Except EngineError (PayloadStatus × Option PayloadError) × Node :=
    (.ok (⟨.accepted, none⟩, none), node.record hash ⟨block, none, .accepted version params⟩)
  let parent := block.2.header.parentHash
  match node.blocks.lookup parent with
  -- Step 4: a payload whose parent is the valid head runs on the chain of that parent.
  --
  -- A payload on another valid parent is accepted.
  | some ⟨_, _, .valid post⟩ =>
    if parent = node.forkchoice.headBlockHash then node.executeOn hash block post version params
    else accept
  -- So is a payload on an accepted parent.
  | some ⟨_, _, .accepted _ _⟩ => accept
  -- Payload validation, step 1: each ancestor must pass validation, as in EIP-3675 block validity.
  --
  -- So a payload whose parent is invalid is invalid too, and the node keeps it as invalid.
  --
  -- Step 3: its latest valid hash is the latest valid block of the chain of its parent.
  --
  -- That hash is zero when that block is of proof of work.
  | some ⟨_, _, .invalid⟩ =>
    (.ok (⟨.invalid, latestValidHash node.tree parent⟩, none),
      node.record hash ⟨block, none, .invalid⟩)
  -- Step 6 of the method: a payload whose parent is unknown lacks requisite data, so it is syncing.
  | none => (.ok (⟨.syncing, none⟩, none), node)

/-- The step of `engine_newPayload`: the status of a payload, with its reason, and the next node.
-/
def newPayloadStep (node : Node) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) × Node :=
  -- The checks before execution run first, and a payload that fails them leaves the node as it was.
  --
  -- They read the other parameters of the request too, so they say nothing of the block alone.
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
      -- Payload validation, step 4: a payload that the node already knows gets that status again.
      --
      -- A known valid payload is valid, with its own hash as the latest valid hash.
      | some ⟨_, _, .valid _⟩ => (.ok (⟨.valid, some hash⟩, none), node)
      -- A known invalid payload is invalid, with the latest valid block of its chain.
      | some ⟨_, _, .invalid⟩ => (.ok (⟨.invalid, latestValidHash node.tree hash⟩, none), node)
      -- Any other payload, even one that the node keeps as accepted, gets the answer of its parent.
      | _ => node.onParent hash ⟨checked.fork, checked.block⟩ version params

/-- The node after it validates the accepted blocks of the chain that ends at a block. -/
def validateChain (node : Node) : Nat → Hash32 → Node
  -- The fuel bounds the number of blocks, and the update gives the number of known blocks.
  | 0, _ => node
  | fuel + 1, hash =>
    match node.blocks.lookup hash with
    | some ⟨block, _, .accepted version params⟩ =>
      -- The blocks run oldest first: the chain up to the parent is validated before the block.
      let node := node.validateChain fuel block.2.header.parentHash
      match node.blocks.lookup block.2.header.parentHash with
      -- Payload validation, step 1: a block runs on its parent once that parent is valid.
      --
      -- A block whose run aborts stays accepted.
      | some ⟨_, _, .valid post⟩ => (node.executeOn hash block post version params).2
      -- Step 1: a block whose parent is then invalid is invalid too.
      | some ⟨_, _, .invalid⟩ => node.record hash ⟨block, none, .invalid⟩
      -- A block whose parent is not known as valid or invalid stays accepted.
      | _ => node
    | _ => node

/-- The node after an update validates the chain of the head that it names. -/
def validateHead (node : Node) (version : Nat) (params : Json) : Node :=
  match forkchoiceUpdatedParams version params with
  | .ok (state, _) => node.validateChain node.blocks.length state.headBlockHash
  -- Parameters that do not decode validate nothing.
  | .error _ => node

/-- Whether an update names a head that the node knows as accepted, which it could not validate. -/
def headAccepted (node : Node) (version : Nat) (params : Json) : Bool :=
  match forkchoiceUpdatedParams version params with
  | .ok (state, _) => (node.blocks.lookup state.headBlockHash).any (·.validity.isAccepted)
  | .error _ => false

/-- The node after an update applies a forkchoice state. -/
def applyForkchoice (node : Node) (state : ForkchoiceState) : Node :=
  { node with
    -- `engine_forkchoiceUpdatedV1`, step 7: the state becomes that of the node.
    forkchoice := state
    -- A finalized hash that is not zero becomes the known finalized block.
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

/-- An update on a node whose head is validated: the response, and the next node. -/
def updateStep (node : Node) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadId) × Node :=
  -- The response is that of the method on the tree of the known blocks and the finalized block.
  let answer := forkchoiceUpdatedCall node.config node.transition version node.tree node.finalized
    params
  -- `engine_forkchoiceUpdatedV1`, step 7: the node applies the state whenever it applies the head.
  --
  -- Step 8: it keeps that state even when the checks of the payload attributes then fail.
  --
  -- Step 6 lets a node refuse a too deep reorganization with `-38006`, and this node never does.
  --
  -- It keeps the state after every valid block, so it takes a reorganization of any depth.
  let next := match node.appliedState version params with
    | some state => node.applyForkchoice state
    | none => node
  (forkchoiceUpdatedResponse <$> answer, next)

/-- The update of `engine_forkchoiceUpdated`, before any build: the response, and the next node. -/
def forkchoiceUpdatedStep (node : Node) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadId) × Node :=
  -- `engine_forkchoiceUpdatedV1`, step 4: the head must be valid before the state is updated.
  --
  -- So the node first validates the accepted blocks of the chain of the head, oldest first.
  let node := node.validateHead version params
  -- Step 9: a head that is still accepted, since a run aborted, is syncing.
  --
  -- Step 4: the update then applies nothing.
  if node.headAccepted version params then (.ok (⟨.syncing, none⟩, none), node)
  -- Otherwise the update runs on the validated node.
  else node.updateStep version params

/-- What the builder of a node chooses for the attributes of a build: its choices and transactions.

The transactions are in the form of an execution payload.

Payload building leaves the transactions and the choices of a build to the node. -/
abbrev Builder := (Σ fork, PayloadAttributes fork) → BuildChoices × List ByteArray

/-- The node after an update that answers a payload ID stores the build of that ID. -/
def storeBuild (node : Node) (builder : Builder) (version : Nat) (params : Json)
    (id : PayloadId) : Node :=
  -- Payload building, step 6: a node that already holds a build under that ID keeps it.
  if (node.builds.lookup id).isSome then node
  else match forkchoiceUpdatedParams version params with
    -- Otherwise the attributes of the request, as the version decodes them, build on the head.
    --
    -- The head is the head of the request, which the update applied, with the state after it.
    | .ok (state, some j) =>
      match payloadAttributesOfVersion version j, node.validState state.headBlockHash with
      | .ok decoded, some post =>
        -- Step 2 starts from no transaction, and step 3 leaves the update of the set to the node.
        --
        -- So the builder of the node gives the transactions, with its choices.
        let (choices, transactions) := builder decoded
        match buildPayloadOnChain (node.chainAt state.headBlockHash post) version decoded choices
            transactions with
        -- The stored build has no blobs and does not ask to override an external builder.
        | .ok ⟨fork, built⟩ =>
          { node with builds := (id, ⟨fork, built, ⟨[], [], []⟩, false⟩) :: node.builds }
        -- The node stores nothing when the build fails, so a request for that ID then fails too.
        | .error _ => node
      | _, _ => node
    | _ => node

/-- The step of `engine_forkchoiceUpdated` on a node that builds: the response, and the next node.

The response and the node are those of the update.

An update that answers a payload ID then stores the build of that ID, with the builder of the node.
-/
def forkchoiceUpdatedBuildStep (node : Node) (builder : Builder) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadId) × Node :=
  match node.forkchoiceUpdatedStep version params with
  | (.ok (status, some id), next) =>
    (.ok (status, some id), next.storeBuild builder version params id)
  | other => other

/-- The step of `engine_getPayload`: the build of a payload ID, and the node as it was.

The trusted setup checks the proofs of the blobs, from version 3. -/
def getPayloadStep (node : Node) (setup : TrustedSetup) (version : Nat) (id : PayloadId) :
    Except GetPayloadError GetPayloadResponse × Node :=
  -- A request for a payload reads the builds, and leaves the node as it was.
  (getPayload node.config setup node.store version id, node)

end Node

end EthLib.Engine
