module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# Proofs: the sync aggregate of a block

A block passes its sync aggregate only with a valid signature of the members that signed.

With no member signing, only the signature of the point at infinity passes.

The step keeps the sizes of the registry and the balances.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- With no key, the check passes exactly for the signature of the point at infinity.

That holds for every signature checks that reject an empty key list, as BLS does. -/
theorem syncAggregateVerify_empty {message signature : ByteArray}
    (rejectsEmpty : checks.fastAggregateVerify #[] message signature = false) :
    syncAggregateVerify checks #[] message signature = true ↔
      signature = Signatures.G2_POINT_AT_INFINITY := by
  simp [syncAggregateVerify, rejectsEmpty]

/-- The checks of BLS reject an empty key list. -/
theorem bls_fastAggregateVerify_empty (message signature : ByteArray) :
    SignatureChecks.bls.fastAggregateVerify #[] message signature = false := by
  simp [SignatureChecks.bls, Signatures.fastAggregateVerify, Id.run]
  rfl

/-- What a successful sync aggregate step checked.

The keys of the members that signed decode, and the signature check passed on them. -/
theorem processSyncAggregate_signed {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ∃ pubkeys signingRoot,
      syncParticipantPubkeys (state.currentSyncCommittee altair) aggregate.syncCommitteeBits =
        .ok pubkeys ∧
      syncAggregateVerify checks pubkeys signingRoot
        (Base.packBytes aggregate.syncCommitteeSignature) = true := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨pubkeys, found, _, _, _, _, _, _, _, verified, _⟩ := computed
  exact ⟨pubkeys, _, found, verified⟩

/-- One step of the sync rewards keeps the sizes of the registry and the balances. -/
theorem sameSizes_applySyncReward {reward proposerReward : Gwei}
    {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward state member = .ok after) :
    SameSizes state after := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨middle, raised, _, _, paid⟩ := computed
    exact (sameSizes_increaseBalance raised).trans (sameSizes_increaseBalance paid)
  · exact sameSizes_decreaseBalance ((liftAccessor_ok).mp computed)

/-- The sync aggregate step keeps the sizes of the registry and the balances. -/
theorem sameSizes_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    SameSizes state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact foldlM_ok_invariant (SameSizes state) (fun _ _ _ hp step =>
    hp.trans (sameSizes_applySyncReward step)) (SameSizes.refl state) folded

end EthLib.Consensus
