module

public import EthLib.Consensus.ForkChoice.Handlers
public import EthLib.Consensus.HonestProposer
public import EthLib.Engine.ExecutionEngine
public import EthLib.Engine.ForkchoiceUpdated

/-!
# `Engine.PreparePayload`

What an honest proposer asks of the execution layer before it proposes a block.

This module covers Bellatrix to Heze.

The proposer sends a forkchoice update with payload attributes.

The head of the update is the parent of its payload.

The execution layer then builds a payload on that head, with those attributes.

The state is the state of the slot of the proposal, before its block.

The safe and the finalized block of the update come from the fork choice, through the caller.

The caller reads the finalized block from the store: the payload of the finalized beacon block.

From Gloas it is the parent payload that the bid of that block builds on.

The call to the execution layer, and the payload that it builds, are not specified here.
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Consensus
open Serialization.Ssz.SszType

variable {preset : Preset} {fork : Fork}

/-! ## The terminal block of proof of work -/

/-- The block of a chain of proof of work with a hash, if the chain holds one.

The chain is a list of blocks, read in order, each found by its own hash.

A hash that two blocks share finds the first of them. -/
def findPowBlock (powChain : List PowBlock) (hash : Hash32) : Option PowBlock :=
  powChain.find? (·.blockHash = hash)

/-- From Bellatrix: the first block of a chain of proof of work that is a valid terminal block.

The blocks are read in the order of the list, so of two blocks that both qualify, the first counts.

The two conditions on the total difficulty are those of [EIP-3675].

[EIP-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/
def getPowBlockAtTerminalTotalDifficulty (config : Config) (powChain : List PowBlock) :
    Except ProposerError (Option PowBlock) :=
  go powChain
where
  /-- The search over the blocks that remain. -/
  go : List PowBlock → Except ProposerError (Option PowBlock)
    -- No block of the chain qualifies, so there is no terminal block yet.
    | [] => .ok none
    | block :: rest =>
      -- EIP-3675: the total difficulty of the block is at least `TERMINAL_TOTAL_DIFFICULTY`.
      if config.TERMINAL_TOTAL_DIFFICULTY ≤ block.totalDifficulty then
        -- Not in EIP-3675: a block whose parent hash is zero has no parent.
        --
        -- So reaching the difficulty suffices.
        if block.parentHash = ZERO_HASH then .ok (some block)
        else
          match findPowBlock powChain block.parentHash with
          -- Not in EIP-3675: a block that reaches the difficulty with no known parent is an error.
          | none => .error (.unknownPowBlock block.parentHash)
          -- EIP-3675: the total difficulty of its parent is below `TERMINAL_TOTAL_DIFFICULTY`.
          | some parent =>
            if isValidTerminalPowBlock config block parent then .ok (some block) else go rest
      else go rest

/-- From Bellatrix: the terminal block of proof of work.

The search fails on a block that reaches the difficulty when the chain does not hold its parent. -/
def getTerminalPowBlock (config : Config) (powChain : List PowBlock) :
    Except ProposerError (Option PowBlock) :=
  -- EIP-3675: `TERMINAL_BLOCK_HASH`, when set, designates the terminal PoW block.
  --
  -- It takes precedence over the search by difficulty, and gives the block of the chain with it.
  if config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH then
    .ok (findPowBlock powChain config.TERMINAL_BLOCK_HASH)
  -- Otherwise it is the first valid terminal block of the chain.
  else getPowBlockAtTerminalTotalDifficulty config powChain

/-! ## The forkchoice update of a proposer -/

/-- From Bellatrix to Fulu: the head of the forkchoice update of a proposer, if it asks for one.

The search for that block can fail, when a block that reaches the difficulty has no known parent. -/
def payloadHeadBlockHash (config : Config) (state : BeaconState preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) (powChain : List PowBlock) :
    Except ProposerError (Option Hash32) :=
  -- After the merge, the head is the block hash of the latest payload header of the state.
  --
  -- From Capella the merge is complete, so the head is that hash without the check.
  if .shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true then
    .ok (some (state.latestExecutionPayloadHeader bellatrix).blockHash)
  -- Before the merge, a configured terminal block hash asks for nothing until its activation epoch.
  --
  -- That epoch is a configuration value of the consensus layer, not of EIP-3675.
  else if config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH ∧
      getCurrentEpoch state < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH then .ok none
  -- Otherwise the head is the terminal PoW block, which the payload builds on to mark the merge.
  --
  -- Without a terminal block yet, the proposer asks for nothing.
  else (getTerminalPowBlock config powChain).map (·.map (·.blockHash))

/-- From Capella: the withdrawals of the payload attributes, which the state expects.

It fails when the expected withdrawals fail. -/
def payloadAttributesWithdrawals (state : BeaconState preset fork) :
    Except ProposerError (Since .shapella fork (List Execution.Blocks.Withdrawal)) :=
  if capella : .shapella ≤ fork then do
    let expected ← (getExpectedWithdrawals state capella).mapError .transition
    return fun _ => expected.withdrawals.toList.map executionWithdrawal
  else .ok fun later => absurd later capella

/-- From Deneb: the root of the parent beacon block, that of the latest block header of the state.

It fails when the header cannot be hashed. -/
def payloadAttributesParentRoot (state : BeaconState preset fork) :
    Except ProposerError (Since .dencun fork Hash32) :=
  if deneb : .dencun ≤ fork then do
    let root ← (hashTreeRoot state.latestBlockHeader).mapError .ssz
    return fun _ => root
  else .ok fun later => absurd later deneb

/-- From Bellatrix to Fulu: the forkchoice update of a proposer, with its payload attributes.

It has no value when the proposer asks for nothing, before the merge.

It fails when the head fails, a 64-bit operation overflows, or the mix, withdrawals or root fail. -/
def prepareExecutionPayload (config : Config) (state : BeaconState preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam)
    (safeBlockHash finalizedBlockHash : Hash32)
    (suggestedFeeRecipient : ExecutionAddress) (powChain : List PowBlock) :
    Except ProposerError (Option (ForkchoiceState × PayloadAttributes fork)) := do
  -- The head of the update, the parent of the payload.
  match ← payloadHeadBlockHash config state bellatrix powChain with
  | none => return none
  | some headBlockHash =>
    -- The timestamp is the time of the slot of the state.
    let timestamp ← (computeTimeAtSlot config state.genesisTime state.slot).mapError .arith
    -- The RANDAO mix is that of the current epoch of the state.
    let prevRandao ← (getRandaoMix state (getCurrentEpoch state)).mapError .accessor
    -- From Capella, the withdrawals that the state expects of the next payload.
    let withdrawals ← payloadAttributesWithdrawals state
    -- From Deneb, the root of the latest block header of the state, the parent of the block.
    let parentBeaconBlockRoot ← payloadAttributesParentRoot state
    -- The head, then the safe and the finalized block that the caller gives.
    --
    -- The fee recipient is the one that the proposer suggests.
    return some (⟨headBlockHash, safeBlockHash, finalizedBlockHash⟩, {
      timestamp, prevRandao, suggestedFeeRecipient, withdrawals, parentBeaconBlockRoot
      -- The fields from Gloas and Heze have no value before Gloas.
      slotNumber := fun gloas => absurd gloas (Nat.not_le_of_lt bellatrix.2)
      targetGasLimit := fun gloas => absurd gloas (Nat.not_le_of_lt bellatrix.2)
      inclusionListTransactions := fun heze =>
        absurd heze (Nat.not_le_of_lt (Nat.lt_trans bellatrix.2 (by decide))) })

/-! ## The forkchoice update of a proposer, from Gloas -/

/-- From Gloas: the parent on which a proposer builds, and the withdrawals of its payload.

A block and its payload arrive apart, so the proposer chooses the full or the empty parent node.

The result is the state that the attributes read, the withdrawals and the head of the update.

It fails when the current slot or the choice fails, or when the store holds no payload to build on.

It also fails when that payload or its withdrawals fail. -/
def payloadParentGloas (config : Config) (checks : SignatureChecks) (store : Store preset fork)
    (head : ForkChoiceNode) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Except ProposerError (BeaconState preset fork × Array Consensus.Withdrawal × Hash32) := do
  -- The latest bid of the state, read before any payload applies.
  let parentBid := state.latestExecutionPayloadBid gloas
  let slot ← (store.getCurrentSlot config).mapError .forkChoice
  -- The fork choice says, at the current slot, whether to build on the full node of the head.
  if ← (store.shouldBuildOnFull gloas head slot).mapError .forkChoice then
    -- The payload that the store holds for the block of the head; none is an error.
    let some envelope := (store.payloads gloas)[head.root]?
      | throw (.forkChoice (.payloadNotVerified head.root))
    -- That payload applies to a copy of the state, before the withdrawals are computed.
    let state ← (applyParentExecutionPayload config checks state gloas
      envelope.executionRequests).mapError .transition
    -- The withdrawals that this new state expects.
    let expected ←
      (getExpectedWithdrawals state (Nat.le_trans (by decide) gloas)).mapError .transition
    -- The head of the update is the block hash of the latest bid.
    return (state, expected.withdrawals, parentBid.blockHash)
  else
    -- On the empty node, the state stays, with the withdrawals that it records.
    --
    -- The head of the update is the parent block hash of the latest bid.
    return (state, (state.payloadExpectedWithdrawals gloas).data, parentBid.parentBlockHash)

/-- From Heze: the transactions of the inclusion lists that a payload on a head must answer to.

It fails at slot 0, or when the dependent root of the slot before fails. -/
def payloadInclusionListTransactions (store : Store preset fork) (state : BeaconState preset fork)
    (headRoot : Root) : Except ProposerError (Since .hegota fork (List InclusionListTransaction)) :=
  if heze : .hegota ≤ fork then do
    -- The lists of the slot before that of the state, on the chain of the head, timely or not.
    let transactions ←
      (getPayloadInclusionListTransactions store heze state headRoot).mapError .duty
    return fun _ => transactions
  else .ok fun later => absurd later heze

/-- From Gloas: the forkchoice update of a proposer, with its payload attributes.

The custody columns of the update are not part of these types.

It fails when the parent fails, a 64-bit operation overflows, or the mix, root or lists fail. -/
def prepareExecutionPayloadGloas (config : Config) (checks : SignatureChecks)
    (store : Store preset fork) (head : ForkChoiceNode) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (safeBlockHash finalizedBlockHash : Hash32)
    (suggestedFeeRecipient : ExecutionAddress) (targetGasLimit : UInt64) :
    Except ProposerError (ForkchoiceState × PayloadAttributes fork) := do
  -- The head and the withdrawals come from the parent on which the proposer builds.
  --
  -- From here the state is the one after the payload of the parent, when the proposer builds on it.
  let (state, withdrawals, headBlockHash) ← payloadParentGloas config checks store head state gloas
  -- The timestamp is the time of the slot of the state.
  let timestamp ← (computeTimeAtSlot config state.genesisTime state.slot).mapError .arith
  -- The RANDAO mix is that of the current epoch of the state.
  let prevRandao ← (getRandaoMix state (getCurrentEpoch state)).mapError .accessor
  -- The root of the latest block header of the state, the parent of the block.
  let parentBeaconBlockRoot ← (hashTreeRoot state.latestBlockHeader).mapError .ssz
  -- From Heze, the transactions of the inclusion lists of the slot before.
  let inclusionListTransactions ← payloadInclusionListTransactions store state head.root
  -- The head, then the safe and the finalized block that the caller gives.
  --
  -- The update may also name the columns that the node custodies, one bit per column.
  --
  -- The guide of the proposer names none, while the fork choice says that a node should name them.
  return (⟨headBlockHash, safeBlockHash, finalizedBlockHash⟩, {
    -- The fee recipient is the one that the proposer suggests.
    timestamp, prevRandao, suggestedFeeRecipient
    withdrawals := fun _ => withdrawals.toList.map executionWithdrawal
    parentBeaconBlockRoot := fun _ => parentBeaconBlockRoot
    -- The slot is the slot of the state.
    slotNumber := fun _ => state.slot
    -- The target of the gas limit is the one that the proposer gives.
    targetGasLimit := fun _ => targetGasLimit
    -- Each transaction goes to the Engine API as its bytes.
    inclusionListTransactions := fun heze =>
      (inclusionListTransactions heze).map fun tx => ⟨tx.data⟩ })

end EthLib.Engine
