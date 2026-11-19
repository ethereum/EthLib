module

public import EthLib.Consensus.Proofs.Proposers
public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Proofs: each proposer of the lookahead is active in its epoch along a run

From Fulu the state keeps the proposers of the current epoch and of the next `MIN_SEED_LOOKAHEAD` ones.

The proposer at position `k` of the lookahead is a validator active in the epoch `k / SLOTS_PER_EPOCH` after the current one.

The upgrade to Fulu draws the lookahead from the registry of the upgrade.

The epoch step shifts the lookahead by one epoch and draws the new last epoch from the registry.

Every other step keeps the lookahead.

The steps keep activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`, which covers the whole lookahead.

So along a run from genesis each entry of the lookahead is active in its epoch.

The proposer of a block is read from the lookahead, so it is active in the epoch of its slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- From Fulu, each entry of the proposer lookahead is active in the epoch of its position.

Position `k` is `k / SLOTS_PER_EPOCH` epochs after the current epoch. -/
def LookaheadActive (state : BeaconState preset fork) : Prop :=
  ∀ fulu : .fusaka ≤ fork,
    ∀ (k : Nat) (inside : k < (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat),
      ∀ epoch : Epoch, epoch.toNat = (getCurrentEpoch state).toNat + k / preset.SLOTS_PER_EPOCH.toNat →
        isActiveAt state epoch ((state.proposerLookahead fulu)[k]'inside).toNat = true

/-- An epoch in the lookahead is no later than the fixed epoch, one epoch on. -/
private theorem lookahead_le_fixed (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤
      preset.MAX_SEED_LOOKAHEAD.toNat)
    {state : BeaconState preset fork} {k : Nat}
    (inside : k < (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)
    {epoch : Epoch} (shift : Nat)
    (he : epoch.toNat = (getCurrentEpoch state).toNat + shift + k / preset.SLOTS_PER_EPOCH.toNat)
    (small : shift ≤ 1) : epoch ≤ activityFixedEpoch state := by
  rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
  have div : k / preset.SLOTS_PER_EPOCH.toNat < preset.MIN_SEED_LOOKAHEAD.toNat + 1 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact inside)
  have := epoch.toNat_lt
  generalize k / preset.SLOTS_PER_EPOCH.toNat = q at he div
  omega

/-- A state of the same epoch and lookahead, with the activity of the first, keeps the invariant. -/
private theorem LookaheadActive.keep {s t : BeaconState preset fork}
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (h : LookaheadActive s) (epoch : getCurrentEpoch t = getCurrentEpoch s)
    (look : t.proposerLookahead = s.proposerLookahead)
    (kept : ActiveKept (activityFixedEpoch s) s t) : LookaheadActive t := by
  intro fulu k inside e he
  rw [epoch] at he
  rw [look, kept e (lookahead_le_fixed covers inside 0 (by simpa using he) (Nat.zero_le _))]
  exact h fulu k inside e he

/-- A block keeps the invariant. -/
private theorem LookaheadActive.processBlock
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (h : LookaheadActive state)
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    LookaheadActive after :=
  h.keep covers (by simp only [getCurrentEpoch, (frame_processBlock ok).slot])
    (processBlock_proposerLookahead ok) (activeKept_processBlock ok)

/-- The upgrade to Fulu draws the lookahead from its own registry, so it starts the invariant. -/
private theorem LookaheadActive.upgradeToFulu {pre : BeaconState preset .pectra}
    {post : BeaconState preset .fusaka} (ok : upgradeToFulu config pre = .ok post) :
    LookaheadActive post := by
  simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨lookahead, drawn, rfl⟩ := ok
  simp only [initializeProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at drawn
  obtain ⟨epochs, mapped, rfl⟩ := drawn
  intro _ k inside e he
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun zero => by simp [zero] at inside
  have div : k / preset.SLOTS_PER_EPOCH.toNat < preset.MIN_SEED_LOOKAHEAD.toNat + 1 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact inside)
  have drawn := vector_mapM_ok_getElem mapped (k / preset.SLOTS_PER_EPOCH.toNat) div
  simp only [Vector.getElem_range, bind_ok_iff, liftArith, mapError_ok_iff] at drawn
  obtain ⟨epoch, counted, drawn⟩ := drawn
  have sum := addChecked_ok_iff.mp counted
  have small : (k / preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat =
      k / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat]
    omega
  have same : e = epoch := UInt64.toNat_inj.mp (by rw [he, sum.2, small]; rfl)
  subst same
  simp only [Vector.getElem_flatten]
  obtain ⟨validator, found, active⟩ := getBeaconProposerIndices_active drawn _
    (Vector.getElem_mem _ |> fun member => by simpa using member)
  exact isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩

end EthLib.Consensus
