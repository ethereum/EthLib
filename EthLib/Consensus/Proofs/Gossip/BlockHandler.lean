module

public import EthLib.Consensus.Gossip.Block
public import EthLib.Consensus.Proofs.ForkChoice.Handlers
public import EthLib.Consensus.Proofs.ForkChoice.Reachable
public import EthLib.Consensus.Proofs.Gossip.Block
public import EthLib.Consensus.Proofs.Gossip.Payload
public import EthLib.Consensus.Proofs.Transition.BlockRoots
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.StateTransition
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the block topic against the block handler

A block that the topic rejects is invalid, and its sender is penalized.

So a check that rejects a block that the block handler accepts penalizes an honest peer.

From Gloas the topic checks the size of each list of operations of a block against its limit.

Before Heze it also rejects a block with a deposit.

In the same way, it checks four lists of requests that the block carries for its parent payload.

It also checks the blob commitments of the bid against the blob limit of the epoch of the block.

From Deneb to Fulu it checks the blob commitments of the block itself against the limit of its fork.

From Fulu that limit is the one of the epoch of the block.

The topic rejects or ignores a block whose parent has no state in the store.

It checks the proposer that the parent state expects at the slot of the block.

From Gloas it checks that the bid of the block names the parent of the block.

It checks that the block comes after its parent block.

From Capella to Fulu it checks the time of the payload against the genesis time of the head state.

From Gloas a block on an empty parent must bid on the execution head of the parent state.

The block handler checks the size of each list of operations against the same limit.

On a full parent it checks the four counts of the requests, and an empty parent takes no request.

Its bid step checks the same blob limit, on a state at the slot of the block.

From Deneb to Fulu its payload step checks the same limit, on a state at the slot of the block.

The handler fails on a block whose parent has no state in the store.

Its header step checks the same proposer, on the parent state advanced to that slot.

From Gloas the parent payload runs before that step, and keeps the proposer.

From Gloas its bid step checks the parent root of the bid against the root at the slot before.

The slots leave the root of the latest block header there, and the steps before the bid keep it.

The header step checks that this root is the parent root of the block.

The last three checks read the parent block, the head state, or the bid of the parent block.

The handler reads the state that the store keeps for the parent.

In a store reached from an anchor at or before the slot of its state, take a kept state.

It comes at or after the slot of its block.

All kept states have one genesis time.

From Gloas each kept state has the bid of its block, or a latest block hash equal to its bid hash.

That needs the anchor state to meet the same condition with the anchor block.

At Bellatrix the topic tests whether payloads run on the head state.

So the timestamp theorem starts at Capella.

A new block that the handler accepts passes the block step of the transition.

So the handler fails on every new block that these checks reject.

It accepts a block that the store holds, whatever its body, so the theorems take a new block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {store : Store preset fork} {sources : BlockSources preset fork}
  {signed : SignedBeaconBlock preset fork} {blockRoot : Root}

/-- A new block that the block handler accepts passes the block step of the transition.

That step runs on the state of its parent, advanced to the slot of the block. -/
theorem processBlock_of_onBlock {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    ∃ pre advanced computed, store.blockStates[signed.message.parentRoot]? = some pre ∧
      processSlots config checks pre signed.message.slot = .ok advanced ∧
      advanced.slot = signed.message.slot ∧
      processBlock config checks sources.engine advanced signed.message = .ok computed := by
  obtain ⟨-, -, pre, _, found, transition, -⟩ := Store.onBlock_new root new added
  obtain ⟨advanced, slots, slot, -, computed, -⟩ := stateTransition_ok transition
  exact ⟨pre, advanced, _, found, slots, slot, computed⟩

/-- From Gloas, a new block that the block handler accepts passes the operation checks of the topic.

So the topic rejects a new block for too many operations or a deposit only if the handler fails. -/
theorem checkBlockBodyLimits_of_onBlock (gloas : .glamsterdam ≤ fork) {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    checkBlockBodyLimits gloas signed.message.body = .accept := by
  obtain ⟨_, _, _, -, -, -, computed⟩ := processBlock_of_onBlock root new added
  obtain ⟨_, _, operatedOk⟩ := processBlock_operations gloas computed
  have noDeposit := processOperations_no_deposit (Nat.le_trans (by decide) gloas) operatedOk
  -- From Gloas the operations step is the Gloas form, which checks each count.
  simp only [processOperations, gloas, ↓reduceDIte] at operatedOk
  obtain ⟨proposers, attesters, attestations, exits, changes, payloads⟩ :=
    processOperationsGloas_counts operatedOk
  unfold checkBlockBodyLimits
  simp only [andThen_eq_accept, rejectUnless_eq_accept, decide_eq_true_eq]
  -- Each limit of the topic is the limit of the handler, so `omega` closes each count.
  refine ⟨by omega, by omega, by omega, ?_, by omega, by omega, by omega⟩
  -- From Heze the deposit check accepts, and before Heze the block holds no deposit.
  split
  · rfl
  · simp [noDeposit]

/-- From Gloas, a new block that the block handler accepts passes the request checks of the topic.

They check four lists of requests that the block carries for its parent payload. -/
theorem checkExecutionRequestsLimits_of_onBlock (gloas : .glamsterdam ≤ fork)
    {after : Store preset fork} (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    checkExecutionRequestsLimits gloas (signed.message.body.parentExecutionRequests gloas) =
      .accept := by
  obtain ⟨_, _, _, -, -, -, computed⟩ := processBlock_of_onBlock root new added
  obtain ⟨_, _, _, _, _, parentOk, -⟩ := processBlock_steps gloas computed
  obtain ⟨withdrawals, consolidations, builderDeposits, exits⟩ :=
    processParentExecutionPayload_counts parentOk
  exact checkExecutionRequestsLimits_eq_accept.mpr
    ⟨withdrawals, consolidations, builderDeposits, exits⟩

/-- From Gloas, a new block that the block handler accepts passes the blob check of the topic.

Its bid commits to at most the blobs per block that the epoch of the block allows. -/
theorem blobKzgCommitments_size_le_of_onBlock (gloas : .glamsterdam ≤ fork)
    {after : Store preset fork} (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    (signed.message.body.signedExecutionPayloadBid gloas).message.blobKzgCommitments.data.size ≤
      (config.getBlobParameters
        (computeEpochAtSlot preset signed.message.slot)).maxBlobsPerBlock.toNat := by
  obtain ⟨_, _, _, -, -, -, computed⟩ := processBlock_of_onBlock root new added
  obtain ⟨_, _, _, _, _, -, headedOk, withdrawnOk, bid, -⟩ := processBlock_steps gloas computed
  obtain ⟨slot, -⟩ := processBlockHeader_checks headedOk
  obtain ⟨-, blobs, -⟩ := checkExecutionPayloadBid_ok_iff.mp (processExecutionPayloadBid_ok bid).1
  -- The header step checks the slot of the block, and the header and withdrawal steps keep it.
  rwa [getCurrentEpoch, (payloadInputs_processWithdrawals withdrawnOk).slot,
    (payloadInputs_processBlockHeader headedOk).slot, ← slot] at blobs

/-- Before Gloas, a new block that the block handler accepts passes the blob check of the topic.

From Deneb it commits to at most the blobs that its fork allows, from Fulu at its epoch. -/
theorem blobCountWithinLimit_of_onBlock (before : fork < .glamsterdam) {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    blobCountWithinLimit config before signed.message = true := by
  by_cases deneb : .dencun ≤ fork
  · obtain ⟨_, _, _, -, -, -, computed⟩ := processBlock_of_onBlock root new added
    obtain ⟨_, _, _, headedOk, withdrawnOk, paidOk⟩ :=
      processBlock_steps_of_lt_gloas (Nat.le_trans (by decide) deneb) before computed
    obtain ⟨slot, -⟩ := processBlockHeader_checks headedOk
    have blobs := processExecutionPayload_blobCommitments paidOk
    -- The header step checks the slot of the block, and the header and withdrawal steps keep it.
    rw [maxBlobsPerBlock, getCurrentEpoch, (payloadInputs_processWithdrawals withdrawnOk).slot,
      (payloadInputs_processBlockHeader headedOk).slot, ← slot] at blobs
    -- So the payload step reads the limit of the topic, from Fulu at the epoch of the block.
    simpa [blobCountWithinLimit, deneb, BeaconBlockBody.blobCommitments] using blobs
  · exact blobCountWithinLimit_of_lt_deneb deneb

/-- A new block that the block handler accepts has a parent with a state in the store.

So the handler fails on every new block whose parent has no state.

The topic rejects or ignores such a block. -/
theorem parentState_of_onBlock {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    ∃ parentState, store.blockStates[signed.message.parentRoot]? = some parentState := by
  obtain ⟨pre, -, -, stored, -⟩ := processBlock_of_onBlock root new added
  exact ⟨pre, stored⟩

/-- A new block that the handler accepts names the proposer that the topic expects.

The topic expects the proposer of the state of the parent, advanced to the slot of the block.

From Gloas the topic advances the parent state and reads its proposer in the same way.

From Gloas the parent payload runs before the header step, and keeps that proposer. -/
theorem expectedProposer_of_onBlock {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after)
    {parentState : BeaconState preset fork}
    (parentKnown : store.blockStates[signed.message.parentRoot]? = some parentState) :
    expectedProposer config checks parentState signed.message.slot =
      .ok signed.message.proposerIndex := by
  obtain ⟨pre, advanced, _, stored, slots, -, computed⟩ := processBlock_of_onBlock root new added
  -- The topic and the handler read the same state of the parent.
  obtain rfl : pre = parentState := Option.some.inj (stored.symm.trans parentKnown)
  by_cases gloas : .glamsterdam ≤ fork
  · obtain ⟨_, _, _, _, _, parentOk, headedOk, -⟩ := processBlock_steps gloas computed
    obtain ⟨-, -, proposer, -⟩ := processBlockHeader_checks headedOk
    rw [getBeaconProposerIndex_processParentExecutionPayload parentOk] at proposer
    simp only [expectedProposer, slots, proposer, bind, Except.bind, Except.mapError]
  · obtain ⟨_, headedOk⟩ := processBlock_header_of_lt_gloas (Nat.lt_of_not_le gloas) computed
    obtain ⟨-, -, proposer, -⟩ := processBlockHeader_checks headedOk
    -- The topic advances that state as the handler does, then reads the same proposer.
    simp only [expectedProposer, slots, proposer, bind, Except.bind, Except.mapError]

/-- From Gloas, a new block that the handler accepts carries a bid on its own parent.

The bid step reads the root at the slot before the block.

The header step checks the parent root against the root of the latest header.

The slots leave the root of the latest block header at that slot, so the two roots agree. -/
theorem bidParentRoot_of_onBlock (gloas : .glamsterdam ≤ fork) {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    (signed.message.body.signedExecutionPayloadBid gloas).message.parentBlockRoot =
      signed.message.parentRoot := by
  obtain ⟨_, advanced, _, -, slots, slot, computed⟩ := processBlock_of_onBlock root new added
  obtain ⟨parented, headed, withdrawn, _, _, parentOk, headedOk, withdrawnOk, biddedOk, -⟩ :=
    processBlock_steps gloas computed
  -- The bid step reads the root at the slot before, in the buffer of the state it runs on.
  obtain ⟨-, -, -, -, -, -, rootOk, -⟩ :=
    checkExecutionPayloadBid_ok_iff.mp (processExecutionPayloadBid_ok biddedOk).1
  obtain ⟨-, read⟩ := getBlockRootAtSlot_read rootOk
  -- The header step reads the root of the latest block header as the parent root.
  have parentRoot := (processBlockHeader_checks headedOk).2.2.2.1
  -- The parent, header and withdrawal steps keep the slot and the buffer of block roots.
  have parent := payloadInputs_processParentExecutionPayload parentOk
  have header := payloadInputs_processBlockHeader headedOk
  have withdrawal := payloadInputs_processWithdrawals withdrawnOk
  have sameSlot : withdrawn.slot = advanced.slot :=
    withdrawal.slot.trans (header.slot.trans parent.slot)
  have sameRoots : withdrawn.blockRoots = advanced.blockRoots :=
    withdrawal.blockRoots.trans (header.blockRoots.trans parent.blockRoots)
  have sameHeader : parented.latestBlockHeader = advanced.latestBlockHeader :=
    parent.latestBlockHeader
  -- The slots leave the root of the latest block header at the slot before the block.
  obtain ⟨latest, hashed, written⟩ := processSlots_latestBlockRoot slots
  rw [sameRoots, sameSlot, slot, written] at read
  rw [sameHeader, hashed] at parentRoot
  exact (Except.ok.inj read).symm.trans (Except.ok.inj parentRoot)

/-- A new block that the handler accepts comes after its parent block.

The state that the store keeps for the parent comes at or after the slot of the parent block. -/
theorem parentSlot_of_onBlock {after : Store preset fork} {orphanParent : Root}
    (linked : store.Linked orphanParent)
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after)
    {parent : BeaconBlock preset fork}
    (parentKnown : store.blocks[signed.message.parentRoot]? = some parent) :
    parent.slot < signed.message.slot := by
  obtain ⟨pre, _, _, stored, slots, -, -⟩ := processBlock_of_onBlock root new added
  obtain ⟨block, blockFound, slotLe⟩ := linked.stateAfter _ _ stored
  -- The store keeps one block for the parent root, and the slots move past the slot of its state.
  obtain rfl : block = parent := Option.some.inj (blockFound.symm.trans parentKnown)
  exact UInt64.lt_of_le_of_lt slotLe (processSlots_slot slots).1

/-- From Capella to Fulu, a new block that the handler accepts carries the time of its slot.

Its payload has the time of the slot of the block.

That time is counted from the genesis time of any kept state.

The topic reads that genesis time from the head state, which the store keeps. -/
theorem payloadTimestamp_of_onBlock (capella : .shapella ≤ fork) (before : fork < .glamsterdam)
    {after : Store preset fork} (oneTime : store.OneGenesisTime)
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after)
    {keptRoot : Root} {kept : BeaconState preset fork}
    (keptFound : store.blockStates[keptRoot]? = some kept) :
    computeTimeAtSlot config kept.genesisTime signed.message.slot =
      .ok (signed.message.body.executionPayload
        ⟨Nat.le_trans (by decide) capella, before⟩).timestamp := by
  obtain ⟨_, _, _, stored, slots, slot, computed⟩ := processBlock_of_onBlock root new added
  obtain ⟨_, _, _, headedOk, withdrawnOk, paidOk⟩ :=
    processBlock_steps_of_lt_gloas capella before computed
  have time := (processExecutionPayload_randao_time paidOk).2
  have header := payloadInputs_processBlockHeader headedOk
  have withdrawal := payloadInputs_processWithdrawals withdrawnOk
  -- The header and withdrawal steps keep the slot and the genesis time of the advanced state.
  rw [withdrawal.slot, header.slot, slot, withdrawal.genesisTime, header.genesisTime,
    processSlots_genesisTime slots, oneTime stored keptFound] at time
  exact time

/-- From Gloas, take a new block on an empty parent that the handler accepts.

It bids on the execution head of the parent.

The topic finds the parent empty from the bid of the parent block.

The handler finds it empty from the latest bid of the parent state, which is the same bid.

The parent payload step then leaves the latest block hash as it is.

That hash is the one of the parent state, advanced to the slot of the block. -/
theorem bidParentHash_of_onBlock (gloas : .glamsterdam ≤ fork) {after : Store preset fork}
    (bids : store.StatesKeepBids)
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after)
    {parent : BeaconBlock preset fork} {parentState advanced : BeaconState preset fork}
    (parentKnown : store.blocks[signed.message.parentRoot]? = some parent)
    (stateKnown : store.blockStates[signed.message.parentRoot]? = some parentState)
    (advancedOk : processSlots config checks parentState signed.message.slot = .ok advanced)
    (empty : Store.parentPayloadStatus signed.message parent ≠ .full) :
    (signed.message.body.signedExecutionPayloadBid gloas).message.parentBlockHash =
      advanced.latestBlockHash gloas := by
  obtain ⟨pre, advanced', _, stored, slots, -, computed⟩ := processBlock_of_onBlock root new added
  -- The handler reads the same parent state, and the slots advance it to the same state.
  have samePre : parentState = pre := Option.some.inj (stateKnown.symm.trans stored)
  subst samePre
  have sameAdvanced : advanced = advanced' := Except.ok.inj (advancedOk.symm.trans slots)
  subst sameAdvanced
  -- The parent state has the bid of the parent block, or a latest block hash equal to its hash.
  obtain ⟨block, blockFound, sameBid⟩ := bids stored
  have sameBlock : parent = block := Option.some.inj (parentKnown.symm.trans blockFound)
  subst sameBlock
  have kept := processSlots_latestBid slots
  simp only [Store.parentPayloadStatus, gloas, ↓reduceDIte] at empty
  by_cases emptyHere :
      (signed.message.body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
        (advanced.latestExecutionPayloadBid gloas).blockHash
  swap
  -- A handler that finds the parent full needs a latest block hash equal to the hash of its bid.
  · have full := Classical.not_not.mp emptyHere
    rcases sameBid gloas with sameBlockBid | hashEq
    · rw [kept.2, sameBlockBid] at full
      simp [full] at empty
    · rw [full, kept.1, kept.2]
      exact hashEq.symm
  -- Otherwise the handler finds the parent empty too, and its parent step keeps the state.
  obtain ⟨parented, _, withdrawn, _, _, parentOk, headedOk, withdrawnOk, biddedOk, -⟩ :=
    processBlock_steps gloas computed
  have sameParented : parented = advanced := by
    cases requests : (signed.message.body.parentExecutionRequests gloas).isEmpty gloas
    · rw [processParentExecutionPayload_of_empty_requests emptyHere requests] at parentOk
      cases parentOk
    · rw [processParentExecutionPayload_of_empty emptyHere requests] at parentOk
      exact (Except.ok.inj parentOk).symm
  subst sameParented
  -- The bid step checks the parent hash against the latest block hash, which the steps keep.
  obtain ⟨-, -, -, -, parentHash, -⟩ :=
    checkExecutionPayloadBid_ok_iff.mp (processExecutionPayloadBid_ok biddedOk).1
  rw [parentHash, (payloadInputs_processWithdrawals withdrawnOk).latestBlockHash,
    (payloadInputs_processBlockHeader headedOk).latestBlockHash]

end EthLib.Consensus
