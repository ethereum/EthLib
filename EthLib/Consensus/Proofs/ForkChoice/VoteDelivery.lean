module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteRecords

/-!
# Conditional delivery of accepted votes

Under synchrony, an honest receiver sees an honest vote one delay after it was sent.

An up-to-date receiver that accepts the attestation records its signer's vote.

The receiver retains a vote of at least that rank at every later event.

Acceptance and agreement on the indexed attestation are explicit hypotheses.

Synchrony alone does not establish handler success.

The network model and voting time follow [arXiv 2405.00549v4, Sections 2 and 3.1][fcr].

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork}
variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- An up-to-date store holds a vote for each non-equivocating signer of an accepted attestation.

The attestation is in its view, and the latest vote has at least the attestation's rank. -/
theorem UpToDate.recorded {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (upToDate : UpToDate config checks sources time view store)
    {attestation : Attestation preset fork} (seen : .attestation attestation ∈ view)
    (accepted : store.onAttestation config checks attestation false = .ok after)
    {indexed : IndexedAttestation preset fork}
    (reads : ReadsAttestation config checks store attestation indexed) {v : ValidatorIndex}
    (voter : v ∈ indexed.attestingIndices.data.toList) (counted : v ∉ store.equivocatingIndices) :
    ∃ m, store.latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  have fixed : after = store := upToDate.2 after (.attestation seen accepted)
  obtain ⟨withTarget, targetState, stored, found, indexedOk, signed⟩ := reads
  have result : after =
      withTarget.updateLatestMessages indexed.attestingIndices.data.toList attestation := by
    unfold Store.onAttestation at accepted
    cases valid : store.validateOnAttestation config attestation false with
    | error err => simp [valid, bind, Except.bind] at accepted
    | ok value =>
      cases value
      simp only [valid, stored, found, indexedOk, signed, bind, Except.bind, Except.mapError,
        ↓reduceIte] at accepted
      cases committees : checkAttestationCommittees targetState attestation <;>
        simp_all [pure, Except.pure]
  have counted' : v ∉ withTarget.equivocatingIndices := by
    simpa [← fixed, result, Store.updateLatestMessages] using counted
  have voted := Store.foldl_recordVote indexed.attestingIndices.data.toList
    withTarget.latestMessages voter counted' (message := LatestMessage.ofAttestation attestation)
  simpa [← fixed, result, Store.updateLatestMessages] using voted

/-- Under synchrony, an up-to-date honest receiver that accepts an honest vote records its signer.

The receiver reads the same indexed attestation and does not count the signer as an equivocator.

Its latest vote has at least the honest vote's rank. -/
theorem VoteAt.recorded {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex} {time n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    {after : Store preset fork}
    (accepted : ((e.world k).state u).onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks ((e.world k).state u) attestation indexed)
    (counted : v ∉ ((e.world k).state u).equivocatingIndices) :
    ∃ m, ((e.world k).state u).latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  have seen := e.mem_view_of_send sync vote.sends honest receiver
    (by simpa [vote.atTime] using late)
  exact upToDate.recorded seen accepted reads (by simp [vote.alone]) counted

/-- A receiver that records an honest vote retains a vote of at least that rank at later events.

The acceptance hypotheses apply at event `k`. -/
theorem VoteAt.recorded_of_le {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex}
    (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex}
    {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    {after : Store preset fork}
    (accepted : ((e.world k).state u).onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks ((e.world k).state u) attestation indexed)
    (counted : v ∉ ((e.world k).state u).equivocatingIndices) {later : ℕ} (le : k ≤ later) :
    ∃ m, ((e.world later).state u).latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  obtain ⟨m, found, rank⟩ := vote.recorded sync honest receiver late upToDate accepted reads counted
  obtain ⟨last, kept, grew⟩ := Execution.latestMessages_rank e le found
  exact ⟨last, kept, UInt64.le_trans rank grew⟩

end EthLib.Consensus.Models.Network
