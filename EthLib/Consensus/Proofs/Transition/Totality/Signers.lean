module

public import EthLib.Consensus.Proofs.Transition.Totality.Justification
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBeforeAltair

/-!
# Proofs: the supply after one epoch, at every fork

One epoch raises the balances and the pending deposits by at most the issuance of a budget.

The bound before Altair is at least the bound from Altair, so it covers every fork.

It holds when the signers of the previous epoch hold at most the total active balance.

That condition holds when no pending attestation is left and no participation flag is set.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The signers of the previous epoch hold at most the balance active in the current epoch.

A validator that exits at the epoch boundary still signs but is no longer active.

So this condition can fail.

A run of slots takes it as an assumption. -/
def SignersWithinActive (state : BeaconState preset fork) : Prop :=
  ∀ total, getTotalActiveBalance state = .ok total →
    -- Before Altair, they are the unslashed signers of pending attestations that match the source.
    (∀ before : fork < .altair, ∀ attestations attesters attestingBalance,
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations →
      getUnslashedAttestingIndices state attestations = .ok attesters →
      getTotalBalance state attesters = .ok attestingBalance → attestingBalance ≤ total) ∧
    -- From Altair, they are, for each participation flag, the unslashed validators that set it.
    ∀ altair : .altair ≤ fork, ∀ flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length,
      ∀ indices participatingBalance,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
          (getPreviousEpoch state) = .ok indices →
      getTotalBalance state indices = .ok participatingBalance → participatingBalance ≤ total

/-- The signers hold at most the total active balance when no one has signed.

Before Altair, both lists of pending attestations must be empty.

From Altair, no participation flag may be set in the previous or the current epoch. -/
theorem SignersWithinActive.of_quiet
    (pending : ∀ before : fork < .altair, (state.previousEpochAttestations before).data = #[] ∧
      (state.currentEpochAttestations before).data = #[])
    (unset : ∀ altair : .altair ≤ fork,
      (∀ flags ∈ (state.previousEpochParticipation altair).data, flags = 0) ∧
        ∀ flags ∈ (state.currentEpochParticipation altair).data, flags = 0) :
    SignersWithinActive state := by
  intro total active
  refine ⟨fun before _ _ _ matching listed weighed => ?_,
    fun altair _ _ _ listed weighed => ?_⟩
  · exact attestingBalance_le_of_empty before (pending before).1 (pending before).2 matching
      listed weighed active
  · exact participatingBalance_le_of_unset altair (unset altair).1 (unset altair).2 listed
      weighed active

/-- One epoch raises the balances and the pending deposits by at most the issuance of a budget.

The bound is that of the rewards before Altair, which is the larger one.

It assumes the signers of the previous epoch hold at most the total active balance. -/
theorem processEpoch_supply_le_of_signers {config : Config} {checks : SignatureChecks}
    -- The registry must be within its limit.
    {budget : Nat} (within : state.RegistryWithinLimit)
    -- The increment must be positive.
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    -- One increment times the base reward factor fits in 64 bits.
    (perIncrement :
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    -- The sum of the effective balances fits in 64 bits.
    (summed : effectiveBalanceSum state < 2 ^ 64)
    -- The budget must be at least one increment and at least the sum of the effective balances.
    (budgeted : max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (effectiveBalanceSum state) ≤ budget)
    -- The participation lists must match the registry.
    --
    -- The pending attestations must resolve.
    (sized : ParticipationMatches state) (resolved : PendingResolved state)
    -- That assumption holds when no one has signed.
    (signers : SignersWithinActive state)
    (computed : processEpoch config checks state = .ok after) :
    balanceSum after + pendingDepositSum after ≤
      balanceSum state + pendingDepositSum state + preset.epochIssuanceBeforeAltair budget := by
  obtain ⟨total, active, _, totalLe⟩ := getTotalActiveBalance_exists_ok within summed
  have totalBudget : total.toNat ≤ budget := by
    rcases totalLe with rfl | le <;> omega
  obtain ⟨beforeSigned, altairSigned⟩ := signers total active
  by_cases altair : Fork.altair ≤ fork
  · -- From Altair, each flag has its participating validators and their balance.
    choose indices listed inside using fun flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length =>
      getUnslashedParticipatingIndices_exists_ok within altair flagIndex.val.toUInt64
        (Or.inl rfl) sized
    choose participatingBalance weighed _ using fun flagIndex =>
      getTotalBalance_exists_ok (inside flagIndex) summed
    have raised := processEpoch_supply_le altair within increment perIncrement active
      (fun flagIndex => ⟨indices flagIndex, listed flagIndex, weighed flagIndex⟩)
      (fun flagIndex => altairSigned altair flagIndex _ _ (listed flagIndex) (weighed flagIndex))
      computed
    have issued := (preset.epochIssuance_le_epochIssuanceBeforeAltair total.toNat).trans
      (preset.epochIssuanceBeforeAltair_mono totalBudget)
    omega
  · -- Before Altair, the pending attestations that match the source have their signers.
    have before : fork < .altair := Nat.lt_of_not_le altair
    have electra : ¬ Fork.pectra ≤ fork := fun electra =>
      altair (Nat.le_trans (by decide) electra)
    have matching := getMatchingSourceAttestations_eq_ok (state := state) before
      (Or.inl rfl)
    obtain ⟨attesters, listed, inside⟩ := getUnslashedAttestingIndices_exists_ok
      fun attestation member => resolved before attestation (mem_recent_of_mem_source member)
    obtain ⟨attestingBalance, weighed, _⟩ := getTotalBalance_exists_ok inside summed
    have raised := processEpoch_supply_le_of_lt_altair before within increment active matching
      listed weighed (beforeSigned before _ _ _ matching listed weighed) computed
    have issued := preset.epochIssuanceBeforeAltair_mono totalBudget
    simp only [pendingDepositSum, electra, ↓reduceDIte]
    omega

end EthLib.Consensus
