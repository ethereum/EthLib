module

public import EthLib.Consensus.Gossip.Block
public import EthLib.Consensus.Proofs.ForkChoice.Handlers
public import EthLib.Consensus.Proofs.Gossip.Block
public import EthLib.Consensus.Proofs.Gossip.Payload
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

Before Gloas it checks the blob commitments of the block itself in the same way.

The block handler checks the size of each list of operations against the same limit.

On a full parent it checks the four counts of the requests, and an empty parent takes no request.

Its bid step checks the same blob limit, on a state at the slot of the block.

Before Gloas its payload step does the same.

So the handler fails on every new block that these checks reject.

It accepts a block that the store holds, whatever its body, so the theorems take a new block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {store : Store preset fork} {sources : BlockSources preset fork}
  {signed : SignedBeaconBlock preset fork} {blockRoot : Root}

/-- From Gloas, a new block that the block handler accepts passes the operation checks of the topic.

So the topic rejects a new block for too many operations or a deposit only if the handler fails. -/
theorem checkBlockBodyLimits_of_onBlock (gloas : .glamsterdam ≤ fork) {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    checkBlockBodyLimits gloas signed.message.body = .accept := by
  obtain ⟨-, -, _, _, -, transition, -⟩ := Store.onBlock_new root new added
  obtain ⟨_, -, -, -, computed, -⟩ := stateTransition_ok transition
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
  obtain ⟨-, -, _, _, -, transition, -⟩ := Store.onBlock_new root new added
  obtain ⟨_, -, -, -, computed, -⟩ := stateTransition_ok transition
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
  obtain ⟨-, -, _, _, -, transition, -⟩ := Store.onBlock_new root new added
  obtain ⟨_, -, -, -, computed, -⟩ := stateTransition_ok transition
  obtain ⟨_, _, _, _, _, -, headedOk, withdrawnOk, bid, -⟩ := processBlock_steps gloas computed
  obtain ⟨slot, -⟩ := processBlockHeader_checks headedOk
  obtain ⟨-, blobs, -⟩ := checkExecutionPayloadBid_ok_iff.mp (processExecutionPayloadBid_ok bid).1
  -- The header step checks the slot of the block, and the header and withdrawal steps keep it.
  rwa [getCurrentEpoch, (payloadInputs_processWithdrawals withdrawnOk).slot,
    (payloadInputs_processBlockHeader headedOk).slot, ← slot] at blobs

/-- Before Gloas, a new block that the block handler accepts passes the blob check of the topic.

From Deneb it commits to at most the blobs per block that the epoch of the block allows. -/
theorem blobCountWithinLimit_of_onBlock (before : fork < .glamsterdam) {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    blobCountWithinLimit config before signed.message = true := by
  by_cases deneb : .dencun ≤ fork
  · obtain ⟨-, -, _, _, -, transition, -⟩ := Store.onBlock_new root new added
    obtain ⟨_, -, -, -, computed, -⟩ := stateTransition_ok transition
    obtain ⟨_, _, _, _, headedOk, withdrawnOk, paidOk⟩ :=
      processBlock_steps_of_lt_gloas (Nat.le_trans (by decide) deneb) before computed
    obtain ⟨slot, -⟩ := processBlockHeader_checks headedOk
    have blobs := processExecutionPayload_blobCommitments paidOk
    -- The header step checks the slot of the block, and the header and withdrawal steps keep it.
    rw [maxBlobsPerBlock, getCurrentEpoch, (payloadInputs_processWithdrawals withdrawnOk).slot,
      (payloadInputs_processBlockHeader headedOk).slot, ← slot] at blobs
    -- So the payload step reads the limit of the topic, from Fulu at the epoch of the block.
    simpa [blobCountWithinLimit, deneb, BeaconBlockBody.blobCommitments] using blobs
  · exact blobCountWithinLimit_of_lt_deneb deneb

end EthLib.Consensus
