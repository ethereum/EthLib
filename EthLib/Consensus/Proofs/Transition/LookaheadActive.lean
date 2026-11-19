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
    {post : BeaconState preset .fusaka} (ok : Consensus.upgradeToFulu config pre = .ok post) :
    LookaheadActive post := by
  simp only [Consensus.upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
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

/-- The epoch of the next slot is the same, or one more when the next slot starts an epoch. -/
private theorem epoch_next {slot next : Slot} (sum : next.toNat = slot.toNat + 1) :
    (next % preset.SLOTS_PER_EPOCH = 0 → next.toNat / preset.SLOTS_PER_EPOCH.toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) ∧
    (next % preset.SLOTS_PER_EPOCH ≠ 0 → next.toNat / preset.SLOTS_PER_EPOCH.toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat) := by
  have divides : next % preset.SLOTS_PER_EPOCH = 0 ↔
      preset.SLOTS_PER_EPOCH.toNat ∣ next.toNat := by
    constructor
    · intro zero
      exact Nat.dvd_of_mod_eq_zero (by simpa using congrArg UInt64.toNat zero)
    · intro divides
      exact UInt64.toNat_inj.mp (by simpa using Nat.mod_eq_zero_of_dvd divides)
  have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat = slot.toNat /
      preset.SLOTS_PER_EPOCH.toNat + if preset.SLOTS_PER_EPOCH.toNat ∣ next.toNat then 1 else 0 := by
    rw [sum]
    exact Nat.succ_div
  exact ⟨fun zero => by rw [step]; simp [divides.mp zero],
    fun nonzero => by
      have not : ¬preset.SLOTS_PER_EPOCH.toNat ∣ next.toNat := fun dvd =>
        nonzero (divides.mpr dvd)
      rw [step]
      simp [not]⟩

/-- A slot keeps the invariant. -/
private theorem LookaheadActive.advanceSlot
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {state after : BeaconState preset fork} (h : LookaheadActive state)
    (ok : Consensus.advanceSlot config checks state = .ok after) : LookaheadActive after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  obtain ⟨boundary, inside⟩ := epoch_next sum
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i end_
    intro fulu k inside e he
    obtain ⟨m, looked, mSlot, mLook, draw, validators, lookEq, -⟩ :=
      processEpoch_lookahead_cut fulu epochedOk
    obtain ⟨ahead, last, aheadEq, drawn, spec⟩ := processProposerLookahead_spec draw
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat :=
      Nat.pos_of_ne_zero fun zero => by simp [zero] at inside
    have epochNext : (getCurrentEpoch ({ epoched with slot := next } : BeaconState preset fork)).toNat =
        (getCurrentEpoch state).toNat + 1 := by
      simp only [getCurrentEpoch_toNat]
      exact boundary end_
    have kept : ActiveKept (activityFixedEpoch state) state
        ({ epoched with slot := next } : BeaconState preset fork) :=
      (ActiveKept.of_validators rfl _).trans
        ((activeKept_processEpoch epochedOk).trans (ActiveKept.of_validators rfl _))
    rw [show ({ epoched with slot := next } : BeaconState preset fork).proposerLookahead fulu =
      looked.proposerLookahead fulu from congrFun lookEq fulu, spec k inside]
    split
    · rename_i shifted
      rw [show m.proposerLookahead fulu = state.proposerLookahead fulu from congrFun mLook fulu,
        kept e (lookahead_le_fixed covers inside 1 (by rw [he, epochNext]) (Nat.le_refl _))]
      exact h fulu (k + preset.SLOTS_PER_EPOCH.toNat) shifted e (by
        rw [Nat.add_div_right _ positive, he, epochNext]; omega)
    · rename_i unshifted
      have curM : (getCurrentEpoch m).toNat = (getCurrentEpoch state).toNat := by
        simp only [getCurrentEpoch_toNat, mSlot]
      have top : k / preset.SLOTS_PER_EPOCH.toNat = preset.MIN_SEED_LOOKAHEAD.toNat :=
        Nat.div_eq_of_lt_le (by
          have := unshifted
          simp only [Nat.not_lt, Nat.add_mul, Nat.one_mul] at this
          omega) inside
      obtain rfl : e = ahead := UInt64.toNat_inj.mp (by
        rw [he, epochNext, top, aheadEq, curM]
        omega)
      rw [isActiveAt_eq_true_iff,
        show ({ epoched with slot := next } : BeaconState preset fork).validators.data =
          m.validators.data from validators]
      exact getBeaconProposerIndices_active drawn _ (by simp)
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    refine h.keep covers (UInt64.toNat_inj.mp ?_) rfl (ActiveKept.of_validators rfl _)
    simp only [getCurrentEpoch_toNat]
    exact inside (fun zero => ‹¬_› zero)

/-- The upgrades keep the invariant, and Fulu starts it. -/
private theorem LookaheadActive.upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : upgradeNext config checks pre = .ok post) (early : post.val.fork < .glamsterdam) :
    LookaheadActive post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok <;>
    first
      | (obtain ⟨_, upgraded, rfl⟩ := ok
         first
           | exact LookaheadActive.upgradeToFulu upgraded
           | exact fun fulu => absurd fulu (by dsimp only; decide)
           | exact absurd early (by dsimp only; decide))
      | (subst ok
         first
           | exact fun fulu => absurd fulu (by dsimp only; decide)
           | exact absurd early (by dsimp only; decide))

/-- A step of a chain keeps the invariant. -/
private theorem LookaheadActive.chainStep
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {x y : ForkedBeaconState preset} (step : ChainStep config checks x y)
    (early : y.fork < .glamsterdam) (h : LookaheadActive x.state) : LookaheadActive y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    exact processUpgrades_induction (config := config) (checks := checks)
      (forked := ⟨x.fork, advanced⟩) (property := fun u => u.fork < .glamsterdam → LookaheadActive u.state)
      (fun _ stepOk later => LookaheadActive.upgradeNext stepOk later)
      (fun _ => h.advanceSlot covers advancedOk) upgraded early
  | block engine signed validated ok =>
    exact h.processBlock covers (applySignedBlock_ok ok).2.1

/-- Along a run from genesis, each proposer of the lookahead is active in its epoch.

The run must end before Gloas.

The preset must have `MAX_SEED_LOOKAHEAD` above `MIN_SEED_LOOKAHEAD`. -/
theorem Run.lookaheadActive {g x : ForkedBeaconState preset}
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (genesis : Genesis config checks g)
    (run : Run config checks g x) (early : x.fork < .glamsterdam) :
    LookaheadActive x.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, initialized⟩ := genesis
    have before := (initializeBeaconStateFromEth1_ok initialized).1
    exact fun fulu => (Nat.not_le_of_lt before (Nat.le_trans (by decide) fulu)).elim
  | snoc pre step ih =>
    exact LookaheadActive.chainStep covers step.chainStep early
      (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early))

/-- A proposer read from the lookahead of a state is active in the epoch of the state. -/
theorem LookaheadActive.proposer_active {state : BeaconState preset fork}
    (fulu : .fusaka ≤ fork) (h : LookaheadActive state) {proposer : ValidatorIndex}
    (ok : getBeaconProposerIndex state = .ok proposer) :
    isActiveAt state (getCurrentEpoch state) proposer.toNat = true := by
  unfold getBeaconProposerIndex at ok
  simp only [fulu, ↓reduceDIte] at ok
  split at ok
  · cases ok
  · rename_i nonzero
    simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    have small := toNat_mod_lt (i := state.slot) nonzero
    exact h fulu _ (Nat.lt_of_lt_of_le small (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
      _ (by rw [Nat.div_eq_of_lt small]; rfl)

end EthLib.Consensus
