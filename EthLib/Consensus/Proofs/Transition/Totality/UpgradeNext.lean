module

public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Totality.Upgrades

/-!
# Proofs: each upgrade to the next fork succeeds under its conditions

The upgrade from each fork to the next has a totality theorem under its own conditions.

The upgrades to Bellatrix, Capella and Deneb only carry fields, so they never fail.

The upgrade to Heze succeeds exactly when the two deposit indices are equal.

The upgrades due at a slot then succeed when a property of states holds at the start.

Each due upgrade must succeed from a state with the property, and keep it.

Before Altair, a run of slots that ends two epochs later clears the pending attestations.

One epoch moves the list of the current epoch to the previous one, and starts an empty list.

So two epochs later both lists are empty, and the upgrade to Altair has none to translate.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The conditions under which the upgrade from the fork of a state to the next fork succeeds.

They are those of the totality theorem of that upgrade.

A fork with no next fork, such as Heze, is never ready, since its upgrade always fails. -/
def UpgradeReady (forked : ForkedBeaconState preset) : Prop :=
  match forked with
  | ⟨.phase0, pre⟩ =>
    (getCurrentEpoch pre).toNat + 1 + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64 ∧
      preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
      preset.SYNC_COMMITTEE_SIZE ≠ 0 ∧ SyncDrawable pre ∧
      ∀ attestation ∈ (pre.previousEpochAttestations (by decide)).data.toList,
        (∃ flags, getAttestationParticipationFlagIndices pre attestation.data
            attestation.inclusionDelay pre.latestBlockHeader.slot = .ok flags) ∧
          ∃ attesters, getPendingAttestingIndices pre attestation = .ok attesters
  | ⟨.altair, _⟩ => True
  | ⟨.bellatrix, _⟩ => True
  | ⟨.shapella, _⟩ => True
  | ⟨.dencun, pre⟩ =>
    BalancesMatch pre ∧ effectiveBalanceSum pre < 2 ^ 64 ∧
      (getCurrentEpoch pre).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat + 1 < 2 ^ 64 ∧
      2 * pre.validators.data.size ≤ preset.PENDING_DEPOSITS_LIMIT.toNat
  | ⟨.pectra, pre⟩ =>
    (getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat +
        preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64 ∧
      preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
      ((getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 ∧
      ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
        ProposersDrawable pre (getCurrentEpoch pre + offset.toUInt64)
  | ⟨.fusaka, pre⟩ =>
    (getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat +
        preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64 ∧
      preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
      ((getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 ∧
      preset.SLOTS_PER_EPOCH ≠ 0 ∧
      (∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
        PtcDrawable pre (getCurrentEpoch pre + offset.toUInt64)) ∧
      pendingAmount (pre.pendingDeposits (by decide)).data.toList < 2 ^ 64
  | ⟨.glamsterdam, pre⟩ =>
    pre.eth1DepositIndex (by decide) = pre.depositRequestsStartIndex (by decide)
  | _ => False

/-- The upgrade to the next fork succeeds under the conditions of that upgrade. -/
theorem upgradeNext_exists_ok {forked : ForkedBeaconState preset}
    (ready : UpgradeReady forked) : ∃ next, upgradeNext config checks forked = .ok next := by
  obtain ⟨fork, pre⟩ := forked
  cases fork with
  | phase0 =>
    obtain ⟨room, look, members, drawable, translated⟩ := ready
    obtain ⟨post, ok⟩ := upgradeToAltair_exists_ok (config := config) room look members
      drawable translated
    exact ⟨⟨⟨.altair, post⟩, (by decide : Fork.phase0 < .altair)⟩, by simp [upgradeNext, ok]⟩
  | altair => exact ⟨_, rfl⟩
  | bellatrix => exact ⟨_, rfl⟩
  | shapella => exact ⟨_, rfl⟩
  | dencun =>
    obtain ⟨matched, summed, room, queue⟩ := ready
    obtain ⟨post, ok⟩ := upgradeToElectra_exists_ok (config := config) matched summed room queue
    exact ⟨⟨⟨.pectra, post⟩, (by decide : Fork.dencun < .pectra)⟩, by simp [upgradeNext, ok]⟩
  | pectra =>
    obtain ⟨seedRoom, look, slotRoom, drawable⟩ := ready
    obtain ⟨post, ok⟩ := upgradeToFulu_ok (config := config) seedRoom look slotRoom drawable
    exact ⟨⟨⟨.fusaka, post⟩, (by decide : Fork.pectra < .fusaka)⟩, by simp [upgradeNext, ok]⟩
  | fusaka =>
    obtain ⟨seedRoom, look, slotRoom, perEpoch, drawable, funded⟩ := ready
    obtain ⟨post, ok⟩ := upgradeToGloas_ok (config := config) (checks := checks) seedRoom
      look slotRoom perEpoch drawable funded
    exact ⟨⟨⟨.glamsterdam, post⟩, (by decide : Fork.fusaka < .glamsterdam)⟩,
      by simp [upgradeNext, ok]⟩
  | glamsterdam =>
    have ok : upgradeToHeze config pre = .ok (upgradeHezeFields config pre) :=
      upgradeToHeze_ok_iff.mpr ⟨ready, rfl⟩
    exact ⟨⟨⟨.hegota, upgradeHezeFields config pre⟩, (by decide : Fork.glamsterdam < .hegota)⟩,
      by simp [upgradeNext, ok]⟩
  | _ => exact ready.elim

/-- The upgrades due at a slot succeed, and keep a property, when each due upgrade does.

The property must hold at the start.

From each state with the property at which an upgrade is due, that upgrade must succeed.

The state it returns must have the property too. -/
theorem processUpgrades_exists_ok {property : ForkedBeaconState preset → Prop}
    {forked : ForkedBeaconState preset} (holds : property forked)
    (step : ∀ reached, property reached → upgradeDue config reached = true →
      ∃ next, upgradeNext config checks reached = .ok next ∧ property next.val) :
    ∃ after, processUpgrades config checks forked = .ok after ∧ property after := by
  fun_induction processUpgrades config checks forked with
  | case1 forked due more =>
    obtain ⟨next, nextOk, nextHolds⟩ := step forked holds due
    obtain ⟨after, afterOk, afterHolds⟩ := more next nextHolds
    refine ⟨after, ?_, afterHolds⟩
    rw [nextOk]
    exact afterOk
  | case2 forked notDue =>
    exact ⟨forked, rfl, holds⟩

/-- Before Altair, one slot keeps or rotates the two lists of pending attestations.

Inside an epoch it keeps both lists.

At an epoch boundary the current list becomes the previous one, and the current list is emptied. -/
theorem advanceSlot_pending {fork : Fork} {state after : BeaconState preset fork}
    (before : fork < .altair) (computed : advanceSlot config checks state = .ok after) :
    ((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat ∧
      after.previousEpochAttestations before = state.previousEpochAttestations before ∧
      after.currentEpochAttestations before = state.currentEpochAttestations before) ∨
    ((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1 ∧
      after.previousEpochAttestations before = state.currentEpochAttestations before ∧
      (after.currentEpochAttestations before).data = #[]) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation before epochedOk
    refine Or.inr ⟨?_, ?_, emptied⟩
    · rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_boundary sum boundary
    · show epoched.previousEpochAttestations before = _
      rw [rotated, cachedEq]
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    · show cached.previousEpochAttestations before = _
      rw [cachedEq]
    · show cached.currentEpochAttestations before = _
      rw [cachedEq]

/-- Before Altair, a run of slots acts on the two lists of pending attestations by its epoch gap.

Within one epoch it keeps both lists.

One epoch later it has rotated them once.

Two or more epochs later both lists are empty. -/
private theorem advanceSlots_pending {fork : Fork} (before : fork < .altair) :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      ((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat →
        after.previousEpochAttestations before = state.previousEpochAttestations before ∧
        after.currentEpochAttestations before = state.currentEpochAttestations before) ∧
      ((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1 →
        after.previousEpochAttestations before = state.currentEpochAttestations before ∧
        (after.currentEpochAttestations before).data = #[]) ∧
      ((getCurrentEpoch state).toNat + 2 ≤ (getCurrentEpoch after).toNat →
        (after.previousEpochAttestations before).data = #[] ∧
        (after.currentEpochAttestations before).data = #[])
  | 0, state, after, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => by omega, fun h => by omega⟩
  | count + 1, state, after, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨mid, midOk, rest⟩ := computed
    obtain ⟨zero, one, two⟩ := advanceSlots_pending before count rest
    have mono : (getCurrentEpoch mid).toNat ≤ (getCurrentEpoch after).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, advanceSlots_slot count rest]
      exact Nat.div_le_div_right (by omega)
    rcases advanceSlot_pending before midOk with ⟨same, prev, cur⟩ | ⟨step, prev, cur⟩
    · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, b⟩ := zero (by omega)
        exact ⟨a.trans prev, b.trans cur⟩
      · obtain ⟨a, b⟩ := one (by omega)
        exact ⟨a.trans cur, b⟩
      · exact two (by omega)
    · refine ⟨fun h => by omega, fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, b⟩ := zero (by omega)
        exact ⟨a.trans prev, by rw [b]; exact cur⟩
      · by_cases h1 : (getCurrentEpoch after).toNat = (getCurrentEpoch mid).toNat + 1
        · obtain ⟨a, b⟩ := one h1
          exact ⟨by rw [a, cur], b⟩
        · exact two (by omega)

/-- Before Altair, a run of slots clears the pending attestations two epochs later.

The epoch at the end must be at least two more than the epoch at the start.

Both the list of the previous epoch and the list of the current epoch are then empty. -/
theorem advanceSlots_pendingAttestations_empty {fork : Fork} {state after : BeaconState preset fork}
    (before : fork < .altair) {count : Nat}
    (computed : advanceSlots config checks count state = .ok after)
    (later : (getCurrentEpoch state).toNat + 2 ≤ (getCurrentEpoch after).toNat) :
    (after.previousEpochAttestations before).data = #[] ∧
      (after.currentEpochAttestations before).data = #[] :=
  (advanceSlots_pending before count computed).2.2 later

end EthLib.Consensus
