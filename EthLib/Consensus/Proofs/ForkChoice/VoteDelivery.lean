module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteRecords
public import EthLib.Consensus.Proofs.Time

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

variable (fork) in
/-- A vote sent at its deadline arrives before the next slot starts. -/
def DelayFits (config : Config) (genesisTimeMs : UInt64) (Δ : ℕ) : Prop :=
  (∃ due, getAttestationDueMs config fork = .ok due) ∧
  ∀ slot next start due following, addChecked slot 1 = .ok next →
    computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    getAttestationDueMs config fork = .ok due →
    computeTimeAtSlotMs config genesisTimeMs next = .ok following →
    start.toNat + due.toNat + Δ < following.toNat

/-- Honest receivers process messages immediately before and at slot boundaries up to `last`.

This is a processing hypothesis, not a consequence of synchrony. -/
def Prompt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (last : ℕ) : Prop :=
  ∀ w ∈ J, ∀ slot start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    e.startTime ≤ start.toNat → start.toNat ≤ last →
    (∃ k, (e.world k).time = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w)) ∧
    (e.startTime < start.toNat → ∃ k, (e.world k).time + 1 = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w))

/-- Processing through a time supplies processing through every earlier time. -/
theorem Prompt.of_le {last later : ℕ} (prompt : Prompt e later) (le : last ≤ later) :
    Prompt e last :=
  fun w honest slot start startOk started bounded =>
    prompt w honest slot start startOk started (bounded.trans le)

/-- A fitting delay leaves time to process a duty vote before the next slot boundary. -/
theorem DelayFits.before_boundary {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {start following : UInt64} {time : ℕ}
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) :
    time + Δ < following.toNat := by
  obtain ⟨start', due, startOk', dueOk, timeEq⟩ := deadline
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  rw [timeEq]
  exact fits.2 slot next start due following nextOk startOk dueOk followingOk

/-- A fitting delay places the attestation deadline inside each representable slot. -/
theorem DelayFits.due_lt_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {start following due : UInt64}
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (dueOk : getAttestationDueMs config fork = .ok due) :
    due < config.SLOT_DURATION_MS := by
  have before := fits.2 slot next start due following nextOk startOk dueOk followingOk
  obtain ⟨start', startOk', startNat, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_refl slot) startOk
  obtain ⟨following', followingOk', followingNat, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_refl next) followingOk
  rw [startOk, Except.ok.injEq] at startOk'
  rw [followingOk, Except.ok.injEq] at followingOk'
  subst start'
  subst following'
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  rw [nextNat, Nat.add_mul, Nat.one_mul] at followingNat
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-- Prompt processing supplies both receiver events around a duty's next slot boundary. -/
theorem Execution.exists_duty_boundaries {Δ : ℕ}
    {slot next : Slot} {start following : UInt64} {time : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e following.toNat)
    {w : ValidatorIndex} (receiver : w ∈ J)
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time)
    (started : e.startTime ≤ time) :
    (∃ k, (e.world k).time + 1 = following.toNat ∧
      time + Δ ≤ (e.world k).time ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w)) ∧
    (∃ k, (e.world k).time = following.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w)) := by
  have before := fits.before_boundary nextOk startOk followingOk deadline
  have startedBefore : e.startTime < following.toNat := by omega
  obtain ⟨boundary, preboundary⟩ :=
    prompt w receiver next following followingOk startedBefore.le (Nat.le_refl _)
  obtain ⟨k, atTime, current⟩ := preboundary startedBefore
  exact ⟨⟨k, atTime, by omega, current⟩, boundary⟩

/-- A duty inside a complete slot interval has a vote before the delivery cutoff. -/
theorem Execution.exists_voteAt_of_duty_interval {Δ : ℕ} {first time : ℕ}
    (votes : ∀ v ∈ J, ∀ slot committeeIndex deadline,
      assignment.committee v slot = some committeeIndex →
      IsAttestationDeadline fork config genesisTimeMs slot deadline →
      e.startTime ≤ deadline → deadline ≤ time →
      ∃ n attestation indexed, VoteAt e v slot committeeIndex deadline n attestation indexed)
    (fits : DelayFits fork config genesisTimeMs Δ)
    {begin last slot : Slot} {beginTime endTime : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endOk : computeTimeAtSlotMs config genesisTimeMs last = .ok endTime)
    (started : e.startTime ≤ first) (fresh : first ≤ beginTime.toNat)
    (complete : endTime.toNat ≤ time)
    {v : ValidatorIndex} (honest : v ∈ J) {committeeIndex : CommitteeIndex}
    (afterBegin : begin ≤ slot) (beforeEnd : slot < last)
    (duty : assignment.committee v slot = some committeeIndex) :
    ∃ next start following deadline n attestation indexed,
      addChecked slot 1 = .ok next ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
      computeTimeAtSlotMs config genesisTimeMs next = .ok following ∧
      IsAttestationDeadline fork config genesisTimeMs slot deadline ∧
      first ≤ deadline ∧ deadline + Δ < following.toNat ∧ following.toNat ≤ time ∧
      VoteAt e v slot committeeIndex deadline n attestation indexed := by
  have slotLt := UInt64.lt_iff_toNat_lt.mp beforeEnd
  have lastBound := last.toNat_lt
  have nextBound : slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by simp; omega
  have nextOk := addChecked_of_lt nextBound
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have nextLe : slot + 1 ≤ last := UInt64.le_iff_toNat_le.mpr (by
    simp only [UInt64.toNat_one] at nextNat; omega)
  obtain ⟨startTime, startOk, startNat, _⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt beforeEnd) endOk
  obtain ⟨following, followingOk, _, followingLe⟩ :=
    exists_timeAtSlotMs_of_le nextLe endOk
  obtain ⟨beginTime', beginOk', _, beginLe⟩ := exists_timeAtSlotMs_of_le afterBegin startOk
  rw [beginOk, Except.ok.injEq] at beginOk'
  subst beginTime'
  obtain ⟨due, dueOk⟩ := fits.1
  have deadline : IsAttestationDeadline fork config genesisTimeMs slot
      (startTime.toNat + due.toNat) := ⟨startTime, due, startOk, dueOk, rfl⟩
  have beginLe := UInt64.le_iff_toNat_le.mp beginLe
  have followingLe := UInt64.le_iff_toNat_le.mp followingLe
  have firstLe : first ≤ startTime.toNat + due.toNat := by omega
  obtain ⟨n, attestation, indexed, vote⟩ := votes v honest slot committeeIndex _ duty deadline
    (started.trans firstLe)
    (by have := fits.before_boundary nextOk startOk followingOk deadline; omega)
  exact ⟨slot + 1, startTime, following, _, n, attestation, indexed,
    nextOk, startOk, followingOk, deadline, firstLe,
    fits.before_boundary nextOk startOk followingOk deadline, by omega, vote⟩

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
