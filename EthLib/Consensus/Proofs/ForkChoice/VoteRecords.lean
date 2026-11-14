module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.ForkChoice.Network
import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins

/-!
# Proofs: the latest vote of a validator never goes back

This module proves that handlers preserve latest votes and never lower their rank.

The paper's latest-vote filter is in [arXiv 2405.00549v4, Section 3.1, LMD-GHOST][fcr].

A store keeps one latest vote for each validator.

A vote replaces it only with a later rank: the target epoch before Gloas, the slot from Gloas.

So no handler removes a latest vote, and none lowers its rank.

An attester slashing adds equivocators, and leaves the latest votes as they are.

Along an execution of the network model, the same holds for each honest validator.

For an implementation comparison, [verified-fast-confirmation][vfc] has two related declarations.

They are `StoreLE` and `Execution.store_latest_message_ge_mono`.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store after : Store preset fork}

/-- An attestation keeps each latest vote, or replaces it with a vote of a later rank. -/
theorem onAttestation_latestMessages_rank {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool} {j : ValidatorIndex}
    {old : LatestMessage fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after)
    (found : store.latestMessages[j]? = some old) :
    ∃ m, after.latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, indexed, _, _, _, attested⟩ := attested
  have kept := (storeTargetCheckpointState_kept storing).1
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact foldl_recordVote_rank indexed.attestingIndices.data.toList (kept ▸ found)
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- A block with its votes keeps each latest vote, or replaces it with a vote of a later rank. -/
theorem onBlockWithVotes_latestMessages_rank {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {j : ValidatorIndex} {old : LatestMessage fork}
    (added : store.onBlockWithVotes config checks sources signed = .ok after)
    (found : store.latestMessages[j]? = some old) :
    ∃ m, after.latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  apply onBlockWithVotes_preserves
    (P := fun s => ∃ m, s.latestMessages[j]? = some m ∧ old.rank ≤ m.rank)
    (holds := ⟨old, found, UInt64.le_refl _⟩) (added := added)
  · intro s s' holds step
    simpa only [(onBlock_checkpointStates_latestMessages step).2] using holds
  · intro s s' a holds step
    obtain ⟨m, held, later⟩ := holds
    obtain ⟨latest, held', later'⟩ := onAttestation_latestMessages_rank step held
    exact ⟨latest, held', UInt64.le_trans later later'⟩
  · intro s s' sl holds step
    simpa only [(onAttesterSlashing_checkpointStates_latestMessages step).2] using holds

end Store

namespace Models.Network

/-- A move of an honest store keeps each latest vote, or replaces it with one of a later rank. -/
theorem Handles.latestMessages_rank {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork} {j : ValidatorIndex} {old : LatestMessage fork}
    (handles : Handles config checks sources time view store after)
    (found : store.latestMessages[j]? = some old) :
    ∃ m, after.latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  cases handles with
  | tick _ _ ticked =>
    exact ⟨old, by simpa only [(Store.onTick_checkpointStates_latestMessages ticked).2]
      using found, UInt64.le_refl _⟩
  | block _ added => exact Store.onBlockWithVotes_latestMessages_rank added found
  | attestation _ attested => exact Store.onAttestation_latestMessages_rank attested found
  | attesterSlashing _ slashed =>
    exact ⟨old, by
      simpa only [(Store.onAttesterSlashing_checkpointStates_latestMessages slashed).2]
        using found, UInt64.le_refl _⟩
  | payloadAttestation _ voted =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ⟨old, found, UInt64.le_refl _⟩
  | envelope _ accepted =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ⟨old, found, UInt64.le_refl _⟩
  | inclusionList _ accepted =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ accepted
    exact ⟨old, found, UInt64.le_refl _⟩

/-- Along an execution, a store keeps each latest vote, or holds one of a later rank.

The network model freezes non-honest local states.

This does not describe arbitrary Byzantine updates to a local state.

The store at a later event holds a vote of that validator, at the same rank or later. -/
theorem Execution.latestMessages_rank {ν κ : Type*} [DecidableEq ν] {config : Config}
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J) {u : ν}
    {n k : ℕ} (le : n ≤ k) {j : ValidatorIndex} {old : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[j]? = some old) :
    ∃ m, ((e.world k).state u).latestMessages[j]? = some m ∧ old.rank ≤ m.rank := by
  induction k, le using Nat.le_induction with
  | base => exact ⟨old, found, UInt64.le_refl _⟩
  | succ k _ ih =>
    rcases e.state_succ k u with same | ⟨_, moved⟩
    · exact same ▸ ih
    · obtain ⟨m, held, later⟩ := ih
      obtain ⟨latest, held', later'⟩ := moved.latestMessages_rank held
      exact ⟨latest, held', UInt64.le_trans later later'⟩

end Models.Network

end EthLib.Consensus
