module

public import EthLib.Consensus.Proofs.Proposers
public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.ProposerLookahead
public import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Proofs: each proposer of the lookahead is active in its epoch along a run

From Fulu the state keeps the proposers of the current epoch and of the epochs after it.

Along a run from genesis, each of them is active in its epoch.

So from Fulu each state of such a run has a proposer for its slot, in the registry.
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
      ∀ epoch : Epoch,
        epoch.toNat = (getCurrentEpoch state).toNat + k / preset.SLOTS_PER_EPOCH.toNat →
        isActiveAt state epoch ((state.proposerLookahead fulu)[k]'inside).toNat = true

/-- An epoch in the lookahead is no later than the fixed epoch, one epoch on. -/
private theorem lookahead_le_fixed (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤
      preset.MAX_SEED_LOOKAHEAD.toNat)
    {state : BeaconState preset fork} {k : Nat}
    (inside : k < (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)
    {epoch : Epoch} (shift : Nat)
    (he : epoch.toNat = (getCurrentEpoch state).toNat + shift + k / preset.SLOTS_PER_EPOCH.toNat)
    (small : shift ≤ 1) : epoch ≤ activityFixedEpoch state := by
  -- The steps keep activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`.
  --
  -- That bound covers the whole lookahead.
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
  -- Every step other than the upgrade to Fulu and the epoch step keeps the lookahead.
  h.keep covers (by simp only [getCurrentEpoch, (frame_processBlock ok).slot])
    (processBlock_proposerLookahead ok) (activeKept_processBlock ok)

/-- The upgrade to Fulu draws the lookahead from its own registry, so it starts the invariant. -/
private theorem LookaheadActive.upgradeToFulu {pre : BeaconState preset .pectra}
    {post : BeaconState preset .fusaka} (ok : Consensus.upgradeToFulu config pre = .ok post) :
    LookaheadActive post := by
  simp only [Consensus.upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨lookahead, drawn, rfl⟩ := ok
  intro _ k inside e he
  obtain ⟨epoch, proposers, epochNat, computed, member⟩ :=
    initializeProposerLookahead_drawn drawn k inside
  obtain rfl : e = epoch := UInt64.toNat_inj.mp (by rw [he, epochNat]; rfl)
  obtain ⟨validator, found, active⟩ := getBeaconProposerIndices_active computed _ member
  exact isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩

/-- A slot keeps the invariant. -/
private theorem LookaheadActive.advanceSlot
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {state after : BeaconState preset fork} (h : LookaheadActive state)
    (ok : Consensus.advanceSlot config checks state = .ok after) : LookaheadActive after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i end_
    intro fulu k inside e he
    obtain ⟨m, looked, mSlot, mLook, draw, validators, lookEq, -⟩ :=
      processEpoch_lookahead_cut fulu epochedOk
    -- The epoch step shifts the lookahead by one epoch.
    --
    -- It draws the new last epoch from the registry.
    obtain ⟨ahead, last, aheadEq, drawn, spec⟩ := processProposerLookahead_spec draw
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat :=
      Nat.pos_of_ne_zero fun zero => by simp [zero] at inside
    have epochNext :
        (getCurrentEpoch ({ epoched with slot := next } : BeaconState preset fork)).toNat =
        (getCurrentEpoch state).toNat + 1 := by
      simp only [getCurrentEpoch_toNat]
      exact nextSlot_epoch_of_boundary sum end_
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
    exact nextSlot_epoch_of_inside sum ‹_›

/-- The upgrades keep the invariant, and Fulu starts it.

From Fulu, an upgrade copies the registry, the slot and the lookahead. -/
private theorem LookaheadActive.upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (h : LookaheadActive pre.state) (ok : upgradeNext config checks pre = .ok post) :
    LookaheadActive post.val.state := by
  by_cases early : .fusaka ≤ pre.fork
  · -- From Fulu, each entry and the validator it names are those of the state before.
    intro late k inside e he
    have held := h early k inside e (by
      rw [he]
      simp only [getCurrentEpoch, (upgradeFrame_upgradeNext ok).slot])
    rw [upgradeNext_proposerLookahead ok early]
    unfold isActiveAt at held ⊢
    rw [upgradeNext_validators_of_electra (Nat.le_trans (by decide) early) ok]
    exact held
  · -- Before Fulu, only the upgrade to Fulu reaches a fork with a lookahead.
    obtain ⟨fork, state⟩ := pre
    change ¬ .fusaka ≤ fork at early
    cases fork <;>
      simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
        throwThe, MonadExceptOf.throw, reduceCtorEq] at ok <;>
      first
        | (obtain ⟨_, upgraded, rfl⟩ := ok
           first
             | exact LookaheadActive.upgradeToFulu upgraded
             | exact fun fulu => absurd fulu (by dsimp only; decide)
             | exact absurd (by decide) early)

/-- A step of a chain keeps the invariant. -/
private theorem LookaheadActive.chainStep
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {x y : ForkedBeaconState preset} (step : ChainStep config checks x y)
    (h : LookaheadActive x.state) : LookaheadActive y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    exact processUpgrades_induction (config := config) (checks := checks)
      (forked := ⟨x.fork, advanced⟩) (property := fun u => LookaheadActive u.state)
      (fun held stepOk => held.upgradeNext stepOk) (h.advanceSlot covers advancedOk) upgraded
  | block engine signed validated ok =>
    exact h.processBlock covers (applySignedBlock_ok ok).2.1

/-- Along a run from genesis, each proposer of the lookahead is active in its epoch.

The preset must have `MAX_SEED_LOOKAHEAD` above `MIN_SEED_LOOKAHEAD`. -/
theorem Run.lookaheadActive {g x : ForkedBeaconState preset}
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (genesis : Genesis config checks g) (run : Run config checks g x) :
    LookaheadActive x.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, initialized⟩ := genesis
    have before := (initializeBeaconStateFromEth1_ok initialized).1
    exact fun fulu => (Nat.not_le_of_lt before (Nat.le_trans (by decide) fulu)).elim
  | snoc pre step ih => exact LookaheadActive.chainStep covers step.chainStep ih

/-- A proposer read from the lookahead of a state is active in the epoch of the state. -/
theorem LookaheadActive.proposer_active {state : BeaconState preset fork}
    (fulu : .fusaka ≤ fork) (h : LookaheadActive state) {proposer : ValidatorIndex}
    (ok : getBeaconProposerIndex state = .ok proposer) :
    isActiveAt state (getCurrentEpoch state) proposer.toNat = true := by
  -- The proposer of a block is read from the lookahead, so it is active in the epoch of its slot.
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

/-- From Fulu, a state that a run reaches from genesis has a proposer for its slot.

That proposer is a validator of the registry.

An epoch of the preset must have at least one slot.

The preset must have `MAX_SEED_LOOKAHEAD` above `MIN_SEED_LOOKAHEAD`. -/
theorem Run.getBeaconProposerIndex_ok {g x : ForkedBeaconState preset}
    (nonzero : preset.SLOTS_PER_EPOCH ≠ 0)
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (genesis : Genesis config checks g) (run : Run config checks g x) (fulu : .fusaka ≤ x.fork) :
    ∃ proposer, getBeaconProposerIndex x.state = .ok proposer ∧
      proposer.toNat < x.state.validators.data.size := by
  -- From Fulu the proposer is an entry of the lookahead, so the read succeeds.
  have read : ∃ proposer, getBeaconProposerIndex x.state = .ok proposer := by
    unfold getBeaconProposerIndex
    simp only [fulu, nonzero, ↓reduceDIte]
    exact ⟨_, rfl⟩
  obtain ⟨proposer, read⟩ := read
  -- That entry is active in the epoch of the state, so the registry holds its validator.
  obtain ⟨_, found, -⟩ := isActiveAt_eq_true_iff.mp
    ((run.lookaheadActive covers genesis).proposer_active fulu read)
  exact ⟨proposer, read, (Array.getElem?_eq_some_iff.mp found).1⟩

end EthLib.Consensus
