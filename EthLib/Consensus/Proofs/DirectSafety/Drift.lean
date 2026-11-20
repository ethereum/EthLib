module

public import EthLib.Consensus.Proofs.DirectSafety.Core
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Drift computed from the concrete transitions

Charge active departures and balance losses separately from recent arrivals and balance gains.

Recent means unslashed and active in either of the two epochs that justification may count.

When the unslashed active keys and their effective balances stay put, the drift is zero.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Exact loss of the unslashed reference stake, outside keys already slashed at this state.

A key already slashed at `x` is not in the reference set, so it is not charged here. -/
noncomputable def referenceLoss (x y : ForkedBeaconState preset) : Nat := by
  classical
  exact ∑ k ∈ (unslashedKeys x.state).filter (¬ SlashedAt y.state ·),
    (effectiveWeight x.state k - Models.supported (recentKeys y.state)
      (effectiveWeight y.state) k)

/-- Exact gains on the voting support over the unslashed reference stake.

Reference stake that just exited is not charged.

A key already slashed at `x` is outside the reference set.

It is absent from this sum only because a slashed flag stays set, which this file does not prove. -/
noncomputable def referenceGain (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ recentKeys y.state,
    (effectiveWeight y.state k - Models.supported (unslashedKeys x.state)
      (effectiveWeight x.state) k)

/-- Unslashed previous-epoch stake that is not active at the current epoch, at one boundary only. -/
noncomputable def boundaryStake (y : ForkedBeaconState preset) : Nat :=
  Models.stake (effectiveWeight y.state) (recentKeys y.state \ activeKeys y.state)

/-- The combined transfer assigns coefficients two, one and two to loss, gain and boundary stake.

In the bound, twice the drift divided by three weighs loss and gain at four thirds and two thirds.

These are the weights of exits and of activations in [EIP-8061], Security Considerations.

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period
-/
noncomputable def stateDrift (x y : ForkedBeaconState preset) : Nat :=
  2 * referenceLoss x y + referenceGain x y + 2 * boundaryStake y

/-- Maximum observed state budget, including the initial state and excluding later epochs. -/
noncomputable def derivedDrift {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y → Nat
  | _, .nil => stateDrift x x
  | y, .snoc pre _ =>
    if (getCurrentEpoch y.state).toNat ≤ high + 1 then
      max (derivedDrift high pre) (stateDrift x y)
    else derivedDrift high pre

/-- The observed drift is at most a bound that grows along the run.

The bound covers every in-horizon prefix. -/
theorem derivedDrift_le_of_prefixes {x y : ForkedBeaconState preset} (high : Nat)
    (startEpoch : (getCurrentEpoch x.state).toNat ≤ high + 1)
    (bound : {u : ForkedBeaconState preset} → Run config checks x u → Nat)
    (grows : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n), Run config checks n y → bound pre ≤ bound (pre.snoc step))
    (covers : ∀ {u : ForkedBeaconState preset} (pre : Run config checks x u),
      Run config checks u y → (getCurrentEpoch u.state).toNat ≤ high + 1 →
        stateDrift x u ≤ bound pre)
    (tail : Run config checks x y) :
    derivedDrift high tail ≤ bound tail := by
  -- Each prefix keeps the suffix to `y`, which `grows` and `covers` read.
  suffices general : ∀ {z : ForkedBeaconState preset} (run : Run config checks x z),
      Run config checks z y → derivedDrift high run ≤ bound run from general tail .nil
  intro z run
  induction run with
  | nil => exact fun post => covers .nil post startEpoch
  | @snoc middle last pre step ih =>
    intro post
    have past := (ih ((Run.nil.snoc step).append post)).trans (grows pre step post)
    simp only [derivedDrift]
    split
    · rename_i within
      exact max_le past (covers (pre.snoc step) post within)
    · exact past

/-- A quorum call of a prefix and a tail is in the tail when its target is not before epoch `low`.

The prefix must end no later than the first slot of epoch `low`.

An epoch has a slot. -/
theorem call_after_reference {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (low : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail)) (later : low ≤ call.target.epoch.toNat) :
    tail.Contains (.slot call.advanced) := by
  rcases (shared.contains_append tail (.slot call.advanced)).mp call.member with member | member
  · exfalso
    -- A call in the shared prefix finishes strictly before the reference slot bound permits.
    obtain ⟨pre, post, _⟩ := shared.contains_split (.slot call.advanced) member
    have afterEnd := post.slot_le
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp call.advanced
    have next := advanceSlot_slot advancedOk
    have kept := processUpgrades_slot upgraded
    have cachedSlot := (frame_processSlot call.cachedOk).slot
    have targetBound : call.target.epoch.toNat ≤
        call.before.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [call.targetEpoch]
      cases call.current <;>
        simp [getPreviousEpoch_toNat, getCurrentEpoch_toNat, cachedSlot]
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
      have := parameters.slots
      omega
    have lowerSlot := (Nat.le_div_iff_mul_le positive).mp (later.trans targetBound)
    rw [← kept] at next
    omega
  · exact member

/-- The unslashed active keys of a state are those of `x`, with the same effective balances.

The unslashed keys active at the current epoch are those of `x` that are not slashed since.

Every unslashed key active at the previous epoch is active at the current epoch.

Each unslashed active key has at this state the effective balance that it has at `x`.

A slashing keeps the set stable: a slashed key leaves both the support and the reference. -/
def StableKeys (x y : ForkedBeaconState preset) : Prop := by
  classical
  exact unslashedKeys y.state = (unslashedKeys x.state).filter (¬ SlashedAt y.state ·) ∧
    recentKeys y.state ⊆ activeKeys y.state ∧
    ∀ key ∈ unslashedKeys y.state, effectiveWeight y.state key = effectiveWeight x.state key

/-- A state at the genesis epoch has stable unslashed active keys against itself.

Its previous epoch is its current epoch, so its recent keys are all active. -/
theorem stableKeys_self_of_genesisEpoch {x : ForkedBeaconState preset}
    (genesisEpoch : getCurrentEpoch x.state = 0) : StableKeys x x := by
  classical
  have previous : getPreviousEpoch x.state = getCurrentEpoch x.state := by
    apply UInt64.toNat_inj.mp
    rw [getPreviousEpoch_toNat, genesisEpoch]
    rfl
  refine ⟨?_, fun key member => ?_, fun _ _ => rfl⟩
  · -- The unslashed keys are already filtered by the slashed flag of the same state.
    ext key
    simp only [unslashedKeys, Finset.mem_filter, and_self, and_assoc]
  · simp only [recentKeys, previous, Finset.mem_filter, Finset.mem_union] at member
    rcases member.1 with active | active
    · exact active
    · exact active

/-- A state with the stable unslashed active keys of `x` has no drift against `x`.

No reference stake is lost, none is gained, and no recent key has left the active set. -/
theorem stateDrift_eq_zero_of_stableKeys {x y : ForkedBeaconState preset}
    (stable : StableKeys x y) : stateDrift x y = 0 := by
  classical
  obtain ⟨same, recent, weights⟩ := stable
  -- The unslashed active keys of `y` are recent at `y`.
  have unslashedRecent : unslashedKeys y.state ⊆ recentKeys y.state := by
    intro key member
    simp only [unslashedKeys, recentKeys, Finset.mem_filter, Finset.mem_union] at member ⊢
    exact ⟨.inl member.1, member.2⟩
  -- Each recent key of `y` is unslashed and active at `y`, so it is an unslashed key of `y`.
  have recentUnslashed : recentKeys y.state ⊆ unslashedKeys y.state := by
    intro key member
    simp only [unslashedKeys, Finset.mem_filter]
    exact ⟨recent member, (Finset.mem_filter.mp member).2⟩
  have loss : referenceLoss x y = 0 := by
    unfold referenceLoss
    refine Finset.sum_eq_zero fun key member => ?_
    -- A reference key not slashed at `y` is an unslashed active key of `y`.
    have kept : key ∈ unslashedKeys y.state := same ▸ member
    simp [Models.supported, unslashedRecent kept, weights key kept]
  have gain : referenceGain x y = 0 := by
    unfold referenceGain
    refine Finset.sum_eq_zero fun key member => ?_
    -- A recent key of `y` is an unslashed key of `y`, hence a reference key.
    have kept := recentUnslashed member
    have inside : key ∈ unslashedKeys x.state := (Finset.mem_filter.mp (same ▸ kept)).1
    simp [Models.supported, inside, weights key kept]
  have boundary : boundaryStake y = 0 := by
    unfold boundaryStake
    rw [Finset.sdiff_eq_empty_iff_subset.mpr recent, Models.stake_empty]
  simp [stateDrift, loss, gain, boundary]

/-- The drift of a tail is zero when its unslashed active keys stay those of `x`.

The epoch of `x` is at most one epoch past the horizon.

Each state of the tail up to one epoch past the horizon, `x` included, has stable keys against `x`.

So no state that the drift reads has lost or gained stake against `x`. -/
theorem derivedDrift_eq_zero_of_stableKeys {x y : ForkedBeaconState preset} (high : Nat)
    (tail : Run config checks x y) (startEpoch : (getCurrentEpoch x.state).toNat ≤ high + 1)
    (stable : ∀ {u : ForkedBeaconState preset} (pre : Run config checks x u)
      (post : Run config checks u y), pre.append post = tail →
        (getCurrentEpoch u.state).toNat ≤ high + 1 → StableKeys x u) :
    derivedDrift high tail = 0 := by
  induction tail with
  | nil => exact stateDrift_eq_zero_of_stableKeys (stable .nil .nil rfl startEpoch)
  | @snoc middle last pre step ih =>
    -- A prefix of the run before the last step is a prefix of the whole run.
    have before := ih fun pre' post joined within =>
      stable pre' (post.snoc step) (by rw [← joined]; rfl) within
    simp only [derivedDrift]
    split
    · rename_i within
      rw [before, stateDrift_eq_zero_of_stableKeys (stable (pre.snoc step) .nil rfl within)]
      rfl
    · exact before

end EthLib.Consensus.DirectSafety
