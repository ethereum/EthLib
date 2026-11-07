module

public import EthLib.Consensus.ForkChoice.Handlers
public import EthLib.Consensus.HonestProposer
public import EthLib.Engine.ExecutionEngine
public import EthLib.Engine.ForkchoiceUpdated

/-!
# `Engine.PreparePayload`

What an honest proposer asks of the execution layer before it proposes a block.

This module covers Bellatrix to Fulu.

The proposer sends a forkchoice update with payload attributes.

The head of the update is the parent of its payload.

The execution layer then builds a payload on that head, with those attributes.

The state is the state of the slot of the proposal, before its block.

The attributes hold the time of the slot of the state, and the RANDAO mix of its epoch.

They also hold the fee recipient that the proposer suggests.

From Capella they hold the withdrawals that the state expects of the next payload.

From Deneb they hold the root of the latest block header of the state, the parent of the block.

Once the merge is complete, and always from Capella, the head is the hash of the latest payload.

Before that, the head is the terminal block of proof of work, and the proposer may not ask at all.

A configured terminal block hash replaces the search for the terminal total difficulty.

That is the rule of [EIP-3675].

Until its activation epoch, the proposer asks nothing.

Otherwise the search reads a chain of proof of work, which the caller gives as a list of blocks.

The safe and the finalized block of the update come from the fork choice, through the caller.

The call to the execution layer, and the payload that it builds, are not specified here.

[EIP-3675]: https://eips.ethereum.org/EIPS/eip-3675#definitions
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Consensus
open Serialization.Ssz.SszType

variable {preset : Preset} {fork : Fork}

/-! ## The terminal block of proof of work -/

/-- The block of a chain of proof of work with a hash, if the chain holds one.

The chain is a list of blocks in the order the guide reads its map, each found by its own hash.

A hash that two blocks share finds the first of them. -/
def findPowBlock (powChain : List PowBlock) (hash : Hash32) : Option PowBlock :=
  powChain.find? (·.blockHash = hash)

/-- From Bellatrix: the first block of a chain of proof of work that is a valid terminal block.

The blocks are read in the order of the list.

A block qualifies when its total difficulty reaches the terminal total difficulty.

Its parent must then have a total difficulty below it.

A block that names the zero hash as its parent needs no parent.

A block that reaches the terminal total difficulty but whose parent is not in the chain is an error.

Two blocks that both qualify give the first. -/
def getPowBlockAtTerminalTotalDifficulty (config : Config) (powChain : List PowBlock) :
    Except ProposerError (Option PowBlock) :=
  go powChain
where
  /-- The search over the blocks that remain. -/
  go : List PowBlock → Except ProposerError (Option PowBlock)
    | [] => .ok none
    | block :: rest =>
      if config.TERMINAL_TOTAL_DIFFICULTY ≤ block.totalDifficulty then
        if block.parentHash = ZERO_HASH then .ok (some block)
        else
          match findPowBlock powChain block.parentHash with
          | none => .error (.unknownPowBlock block.parentHash)
          | some parent =>
            if isValidTerminalPowBlock config block parent then .ok (some block) else go rest
      else go rest

/-- From Bellatrix: the terminal block of proof of work.

A configured terminal block hash names it, and it is the block of the chain with that hash, if any.

Otherwise it is the first block of the chain that reaches the terminal total difficulty first. -/
def getTerminalPowBlock (config : Config) (powChain : List PowBlock) :
    Except ProposerError (Option PowBlock) :=
  if config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH then
    .ok (findPowBlock powChain config.TERMINAL_BLOCK_HASH)
  else getPowBlockAtTerminalTotalDifficulty config powChain

/-! ## The forkchoice update of a proposer -/

/-- From Bellatrix to Fulu: the head of the forkchoice update of a proposer, if it asks for one.

Once the merge is complete, and always from Capella, it is the block hash of the latest payload.

Before the merge, a terminal block hash that is configured but not yet active asks for nothing.

Otherwise the head is the terminal block of proof of work, and there is none without it.

The search for that block can fail, when a block that reaches the difficulty has no known parent. -/
def payloadHeadBlockHash (config : Config) (state : BeaconState preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) (powChain : List PowBlock) :
    Except ProposerError (Option Hash32) :=
  if .shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true then
    .ok (some (state.latestExecutionPayloadHeader bellatrix).blockHash)
  else if config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH ∧
      getCurrentEpoch state < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH then .ok none
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

The head is the parent of the payload, and the safe and the finalized block are given.

The timestamp is the time of the slot of the state, and the RANDAO mix is that of its epoch.

From Capella the withdrawals are those the state expects.

From Deneb the parent root is the root of its latest block header.

It fails when the head fails, a 64-bit operation overflows, or the mix, withdrawals or root fail. -/
def prepareExecutionPayload (config : Config) (state : BeaconState preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam)
    (safeBlockHash finalizedBlockHash : Hash32)
    (suggestedFeeRecipient : ExecutionAddress) (powChain : List PowBlock) :
    Except ProposerError (Option (ForkchoiceState × PayloadAttributes fork)) := do
  match ← payloadHeadBlockHash config state bellatrix powChain with
  | none => return none
  | some headBlockHash =>
    let timestamp ← (computeTimeAtSlot config state.genesisTime state.slot).mapError .arith
    let prevRandao ← (getRandaoMix state (getCurrentEpoch state)).mapError .accessor
    let withdrawals ← payloadAttributesWithdrawals state
    let parentBeaconBlockRoot ← payloadAttributesParentRoot state
    return some (⟨headBlockHash, safeBlockHash, finalizedBlockHash⟩, {
      timestamp, prevRandao, suggestedFeeRecipient, withdrawals, parentBeaconBlockRoot
      slotNumber := fun gloas => absurd gloas (Nat.not_le_of_lt bellatrix.2)
      targetGasLimit := fun gloas => absurd gloas (Nat.not_le_of_lt bellatrix.2) })

end EthLib.Engine
