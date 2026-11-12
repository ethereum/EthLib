module

public import EthLib.Consensus.Proofs.DirectSafety.Core
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Drift computed from the concrete transitions

Charge active departures and balance losses separately from recent arrivals and balance gains.

Recent means active in either of the two epochs whose attestations justification may count.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Exact reference loss outside keys already slashed at this state. -/
noncomputable def referenceLoss (x y : ForkedBeaconState preset) : Nat := by
  classical
  let unslashed := (activeKeys x.state).filter fun k =>
    ¬ ∃ v ∈ y.state.validators.data.toList, v.pubkey = k ∧ v.slashed = true
  exact ∑ k ∈ unslashed,
    (effectiveWeight x.state k - Models.supported (recentKeys y.state)
      (effectiveWeight y.state) k)

/-- Exact gains on the voting support, without charging reference stake that just exited. -/
noncomputable def referenceGain (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ recentKeys y.state,
    (effectiveWeight y.state k - Models.supported (activeKeys x.state)
      (effectiveWeight x.state) k)

/-- Previous-epoch stake outside the current quorum denominator, at one boundary only. -/
noncomputable def boundaryStake (y : ForkedBeaconState preset) : Nat :=
  Models.stake (effectiveWeight y.state) (recentKeys y.state \ activeKeys y.state)

/-- The combined transfer assigns coefficients two, one and two to loss, gain and boundary stake.

Divided by three, loss and gain weigh four thirds and two thirds.

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

end EthLib.Consensus.DirectSafety
