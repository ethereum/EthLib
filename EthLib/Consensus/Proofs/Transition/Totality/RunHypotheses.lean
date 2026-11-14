module

public import EthLib.Consensus.Proofs.Transition.Totality.EpochElectra
public import EthLib.Consensus.Proofs.Transition.Totality.Quiet
public import EthLib.Consensus.Transition.Genesis

/-!
# Proofs: the hypotheses that a run of slots takes on the states it reaches

A run of slots succeeds under bounds that each epoch keeps, and under three more hypotheses.

They are not consequences of the bounds, so a run takes them as assumptions.

The first bounds the signers of the first two epochs by the total active balance.

A validator that exits at the epoch boundary still counts as a signer but is not active.

The run applies no block, so from the third epoch no one has signed and the bound holds.

The second asks that each draw of committees and proposers ends.

A draw is certain to end when it meets a validator at the cap of its fork.

The validators at the cap can leave or lose balance during the run, so a leak breaks that form.

Without a validator at the cap, whether a draw ends depends on the hashes.

In the random oracle model, a search of at most `2^32` members fails with chance below `2^-128`.

That needs a fresh cache and at least one candidate.

That is a bound on a probability, so the end of each draw stays a hypothesis.

The same hypothesis carries the condition of the upgrade to Heze: its two deposit indices are equal.

The third bounds the epochs of a run that starts before Altair.

Before Altair, the inactivity penalty grows with the epochs since the last finality.

It fits when the epoch is at most a limit, about `9 * 10^6` epochs on mainnet.

A run that stays before Altair on a quiet state meets all three, since nothing is drawn there.

It meets the draws in their form at the cap, which gives the end of each draw.

That shows only that the three are consistent, not that the draws from Altair can be met.
-/

@[expose] public section

namespace EthLib.Consensus

open Base EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## The draws at the cap -/

/-- The draws of an epoch transition stop at a validator at the cap, at the states they read.

Each draw reads the state that the stages before it reach.

From Altair, when the next epoch starts a sync committee period, a new committee is drawn.

Every key of the state it reads must then pass validation.

That state must also hold a validator at the cap, active in the next epoch.

From Fulu, the proposers of the epoch one past the seed lookahead are drawn.

The state that step reads must hold a validator at the cap, active then, and unslashed from Gloas.

From Gloas, the payload committees of the slots of that epoch are drawn.

In each slot, one member of the beacon committees must be at the cap. -/
structure EpochDraws (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Prop where
  /-- From Altair, at a sync committee period, every key that the draw reads is valid. -/
  keys : .altair ≤ fork →
    (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
    ∀ ready, run (action config checks) readyStages state = .ok ready →
      ∀ validator ∈ ready.validators.data,
        ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point
  /-- From Altair, at a sync committee period, a validator at the cap is active next epoch. -/
  sync : .altair ≤ fork →
    (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
    ∀ ready, run (action config checks) readyStages state = .ok ready →
      ∃ validator ∈ ready.validators.data,
        isActiveValidator validator (getCurrentEpoch state + 1) ∧
          validator.effectiveBalance.toNat = drawCap preset fork
  /-- From Fulu, a validator at the cap is active one epoch past the seed lookahead. -/
  proposers : .fusaka ≤ fork → ∀ synced,
    run (action config checks) (readyStages ++ [.syncCommittees]) state = .ok synced →
      ∃ validator ∈ synced.validators.data,
        isActiveValidator validator (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1) ∧
          (.glamsterdam ≤ fork → validator.slashed = false) ∧
          validator.effectiveBalance.toNat = drawCap preset fork
  /-- From Gloas, in each slot of that epoch, a member of the beacon committees is at the cap. -/
  ptc : .glamsterdam ≤ fork → ∀ moved,
    run (action config checks) (readyStages ++ [.syncCommittees, .proposerLookahead]) state =
        .ok moved →
      ∀ slot, computeEpochAtSlot preset slot =
          getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1 →
        ∀ members, slotCommitteeMembers moved slot = .ok members →
          ∃ index ∈ members, ∃ validator, getValidator moved index = .ok validator ∧
            validator.effectiveBalance.toNat = drawCap preset fork

/-- The draws of the upgrade from the fork of a state stop at a validator at the cap.

The upgrade to Altair draws a sync committee.

Every key must pass validation, and a validator at the cap must be active in the next epoch.

The upgrade to Fulu draws the proposers of the epochs up to the seed lookahead.

In each such epoch a validator at the cap must be active.

The upgrade to Gloas draws the payload committees of the slots of those epochs.

In each slot, one member of the beacon committees must be at the cap.

The upgrade to Heze also needs its two deposit indices equal, which no draw gives. -/
def UpgradeDraws (forked : ForkedBeaconState preset) : Prop :=
  match forked with
  | ⟨.phase0, pre⟩ =>
    (∀ validator ∈ pre.validators.data,
      ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point) ∧
    ∃ validator ∈ pre.validators.data, isActiveValidator validator (getCurrentEpoch pre + 1) ∧
      validator.effectiveBalance.toNat = drawCap preset .phase0
  | ⟨.pectra, pre⟩ =>
    ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat, ∃ validator ∈ pre.validators.data,
      isActiveValidator validator (getCurrentEpoch pre + offset.toUInt64) ∧
        validator.effectiveBalance.toNat = drawCap preset .pectra
  | ⟨.fusaka, pre⟩ =>
    ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat, ∀ slot,
      computeEpochAtSlot preset slot = getCurrentEpoch pre + offset.toUInt64 →
      ∀ members, slotCommitteeMembers pre slot = .ok members →
        ∃ index ∈ members, ∃ validator, getValidator pre index = .ok validator ∧
          validator.effectiveBalance.toNat = drawCap preset .fusaka
  | ⟨.glamsterdam, pre⟩ =>
    pre.eth1DepositIndex (by decide) = pre.depositRequestsStartIndex (by decide)
  | _ => True

/-- The states that the upgrades due at a slot pass through, from a given state.

The given state is one of them, and so is the result of each due upgrade from one of them. -/
inductive UpgradesPass (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Prop
  | refl (forked : ForkedBeaconState preset) : UpgradesPass config checks forked forked
  | step {forked reached : ForkedBeaconState preset}
      {next : {post : ForkedBeaconState preset // forked.fork < post.fork}}
      (due : upgradeDue config forked = true)
      (computed : upgradeNext config checks forked = .ok next)
      (rest : UpgradesPass config checks next.val reached) :
      UpgradesPass config checks forked reached

/-- The draws of a run of slots stop at a validator at the cap, at each state they read.

Each state that the run reaches before its end must allow the draws of its next slot.

At the end of an epoch, the epoch transition reads the state with the roots of the slot cached.

The upgrades due at the next slot read the states they pass through. -/
def DrawsAtCap (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset)
    (count : Nat) : Prop :=
  ∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
    ((reached.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot reached.state = .ok cached → EpochDraws config checks cached) ∧
    ∀ advanced, advanceSlot config checks reached.state = .ok advanced →
      ∀ upgrading, UpgradesPass config checks ⟨reached.fork, advanced⟩ upgrading →
        upgradeDue config upgrading = true → UpgradeDraws upgrading

/-! ## The draws end -/

/-- The draws of an epoch transition end, at the states they read.

Each draw reads the state that the stages before it reach.

The run proves bounds on that state, and each draw must end under them.

No effective balance is above the cap of the draw, and the registry holds at most `2^40` validators.

The size of a sync committee or a payload committee, times the validators, is below `2^64`.

From Altair, at a sync committee period, every key of the state it reads must also be valid. -/
structure EpochDrawsEnd (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Prop where
  /-- From Altair, at a sync committee period, every key that the draw reads is valid. -/
  keys : .altair ≤ fork →
    (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
    ∀ ready, run (action config checks) readyStages state = .ok ready →
      ∀ validator ∈ ready.validators.data,
        ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point
  /-- From Altair, at a sync committee period, the draw of the next committee ends. -/
  sync : .altair ≤ fork →
    (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
    ∀ ready, run (action config checks) readyStages state = .ok ready →
      (∀ validator ∈ ready.validators.data,
        validator.effectiveBalance.toNat ≤ drawCap preset fork) →
      ready.validators.data.size ≤ 2 ^ 40 →
      preset.SYNC_COMMITTEE_SIZE.toNat * ready.validators.data.size < 2 ^ 64 →
      SyncDrawEnds ready (getCurrentEpoch state + 1)
  /-- From Fulu, the draws of the proposers one epoch past the seed lookahead end. -/
  proposers : .fusaka ≤ fork → ∀ synced,
    run (action config checks) (readyStages ++ [.syncCommittees]) state = .ok synced →
      (∀ validator ∈ synced.validators.data,
        validator.effectiveBalance.toNat ≤ drawCap preset fork) →
      synced.validators.data.size ≤ 2 ^ 40 →
      ProposersDrawEnd synced (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1)
  /-- From Gloas, the draws of the payload committees of that epoch end. -/
  ptc : .glamsterdam ≤ fork → ∀ moved,
    run (action config checks) (readyStages ++ [.syncCommittees, .proposerLookahead]) state =
        .ok moved →
      (∀ validator ∈ moved.validators.data,
        validator.effectiveBalance.toNat ≤ drawCap preset fork) →
      moved.validators.data.size ≤ 2 ^ 40 →
      preset.PTC_SIZE.toNat * moved.validators.data.size < 2 ^ 64 →
      PtcDrawsEnd moved (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1)

/-- The draws of the upgrade from the fork of a state end, under the bounds that it reads.

No effective balance is above the cap of the draw, and the registry holds at most `2^40` validators.

The size of a sync committee or a payload committee, times the validators, is below `2^64`.

The upgrade to Altair draws a sync committee, and every key must also pass validation.

The upgrade to Fulu draws the proposers of the epochs up to the seed lookahead.

The upgrade to Gloas draws the payload committees of the slots of those epochs.

The upgrade to Heze also needs its two deposit indices equal, which no draw gives. -/
def UpgradeDrawsEnd (forked : ForkedBeaconState preset) : Prop :=
  match forked with
  | ⟨.phase0, pre⟩ =>
    (∀ validator ∈ pre.validators.data,
      ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point) ∧
    ((∀ validator ∈ pre.validators.data,
        validator.effectiveBalance.toNat ≤ drawCap preset .phase0) →
      pre.validators.data.size ≤ 2 ^ 40 →
      preset.SYNC_COMMITTEE_SIZE.toNat * pre.validators.data.size < 2 ^ 64 →
      SyncDrawEnds pre (getCurrentEpoch pre + 1))
  | ⟨.pectra, pre⟩ =>
    ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
      (∀ validator ∈ pre.validators.data,
        validator.effectiveBalance.toNat ≤ drawCap preset .pectra) →
      pre.validators.data.size ≤ 2 ^ 40 →
      ProposersDrawEnd pre (getCurrentEpoch pre + offset.toUInt64)
  | ⟨.fusaka, pre⟩ =>
    ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
      (∀ validator ∈ pre.validators.data,
        validator.effectiveBalance.toNat ≤ drawCap preset .fusaka) →
      pre.validators.data.size ≤ 2 ^ 40 →
      preset.PTC_SIZE.toNat * pre.validators.data.size < 2 ^ 64 →
      PtcDrawsEnd pre (getCurrentEpoch pre + offset.toUInt64)
  | ⟨.glamsterdam, pre⟩ =>
    pre.eth1DepositIndex (by decide) = pre.depositRequestsStartIndex (by decide)
  | _ => True

/-- The draws of a run of slots end, at each state they read.

Each state that the run reaches before its end must let the draws of its next slot end.

At the end of an epoch, the epoch transition reads the state with the roots of the slot cached.

The upgrades due at the next slot read the states they pass through.

This holds when each draw meets a validator at the cap of its fork.

In the random oracle model, a search of at most `2^32` members fails with chance below `2^-128`.

That needs a fresh cache and at least one candidate.

That bound is not a deterministic fact, and no theorem sums it over the draws of a run. -/
def DrawsEnd (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset)
    (count : Nat) : Prop :=
  ∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
    ((reached.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot reached.state = .ok cached → EpochDrawsEnd config checks cached) ∧
    ∀ advanced, advanceSlot config checks reached.state = .ok advanced →
      ∀ upgrading, UpgradesPass config checks ⟨reached.fork, advanced⟩ upgrading →
        upgradeDue config upgrading = true → UpgradeDrawsEnd upgrading

/-- The draws of an epoch end when each meets a validator at the cap of its fork.

The products of each draw fit in 64 bits. -/
theorem EpochDraws.drawsEnd {state : BeaconState preset fork} (fits : DrawFits preset fork)
    (draws : EpochDraws config checks state) : EpochDrawsEnd config checks state where
  keys := draws.keys
  sync altair boundary ready ran capped few room :=
    SyncDrawEnds.of_atCap fits capped (draws.sync altair boundary ready ran) few room
  proposers fulu synced ran capped few :=
    ProposersDrawEnd.of_atCap fits capped (draws.proposers fulu synced ran) few
  ptc gloas moved ran capped few room :=
    PtcDrawsEnd.of_atCap fits capped (draws.ptc gloas moved ran) few room

/-- The draws of an upgrade end when each meets a validator at the cap of its fork.

The products of each draw fit in 64 bits. -/
theorem UpgradeDraws.drawsEnd {forked : ForkedBeaconState preset}
    (fits : ∀ fork, DrawFits preset fork) (draws : UpgradeDraws forked) :
    UpgradeDrawsEnd forked := by
  obtain ⟨fork, pre⟩ := forked
  cases fork with
  | phase0 =>
    obtain ⟨keys, full⟩ := draws
    exact ⟨keys, fun capped few room => SyncDrawEnds.of_atCap (fits _) capped full few room⟩
  | pectra =>
    -- Before Gloas no candidate is dropped for being slashed.
    exact fun offset le capped few => ProposersDrawEnd.of_atCap (fits _) capped
      (by
        obtain ⟨validator, member, active, atCap⟩ := draws offset le
        exact ⟨validator, member, active, fun gloas => absurd gloas (by decide), atCap⟩)
      few
  | fusaka =>
    exact fun offset le capped few room =>
      PtcDrawsEnd.of_atCap (fits _) capped (draws offset le) few room
  | glamsterdam => exact draws
  | _ => trivial

/-- The draws of a run end when each meets a validator at the cap of its fork.

The products of each draw fit in 64 bits. -/
theorem DrawsAtCap.drawsEnd {forked : ForkedBeaconState preset} {count : Nat}
    (fits : ∀ fork, DrawFits preset fork) (draws : DrawsAtCap config checks forked count) :
    DrawsEnd config checks forked count := fun steps lt reached advanced =>
  ⟨fun last cached ok => ((draws steps lt reached advanced).1 last cached ok).drawsEnd (fits _),
    fun next ok upgrading pass due =>
      ((draws steps lt reached advanced).2 next ok upgrading pass due).drawsEnd fits⟩

/-! ## The signers of the first two epochs -/

/-- In the first two epochs of a run, the signers hold at most the total active balance.

The condition reads the state at the end of each of those epochs, with the roots cached. -/
def SignersEarly (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset)
    (count : Nat) : Prop :=
  ∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
    (getCurrentEpoch reached.state).toNat < (getCurrentEpoch forked.state).toNat + 2 →
    (reached.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
    ∀ cached, processSlot reached.state = .ok cached → SignersWithinActive cached

/-! ## The epochs before Altair -/

/-- The largest epoch at which the penalties before Altair fit in 64 bits.

The penalties of a validator are at most seven base rewards of the largest cap.

The inactivity penalty multiplies the balance by the epochs since the last finality, then divides.

That count is at most the epoch, so the cap times the epoch must fit with the seven rewards. -/
def Preset.epochLimitBeforeAltair (preset : Preset) : Nat :=
  (2 ^ 64 - 1 - 7 * preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance) /
    preset.largestEffectiveBalance

/-- When seven base rewards fit, the penalties before Altair fit in 64 bits up to the limit. -/
theorem Preset.penalties_lt_of_le_epochLimitBeforeAltair {preset : Preset} {epochBound : Nat}
    (within : epochBound ≤ preset.epochLimitBeforeAltair)
    (rewards : 7 * preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance < 2 ^ 64) :
    7 * preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance +
      preset.largestEffectiveBalance * epochBound < 2 ^ 64 := by
  -- The cap times the limit is at most the room left by the seven rewards.
  have scaled := Nat.mul_le_mul_left preset.largestEffectiveBalance within
  have floor := Nat.mul_div_le (2 ^ 64 - 1 -
    7 * preset.baseRewardBoundBeforeAltair preset.largestEffectiveBalance)
    preset.largestEffectiveBalance
  unfold Preset.epochLimitBeforeAltair at scaled
  omega

/-- On mainnet, the limit before Altair is at least `9 * 10^6` epochs, about 109 years. -/
theorem Preset.epochLimitBeforeAltair_mainnet :
    9000000 ≤ Preset.mainnet.epochLimitBeforeAltair := by
  have root : (Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat).sqrt = 31622 :=
    (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  simp only [Preset.epochLimitBeforeAltair, Preset.baseRewardBoundBeforeAltair, root]
  decide

/-- A run that starts before Altair ends at an epoch within the limit before Altair. -/
def EpochLimitBeforeAltair (forked : ForkedBeaconState preset) (count : Nat) : Prop :=
  forked.fork < .altair →
    (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤
      preset.epochLimitBeforeAltair

/-! ## The three hold together -/

/-- Before the Altair fork epoch, no upgrade is due from Phase 0. -/
private theorem upgradeDue_phase0 {state : BeaconState preset .phase0}
    (before : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat < config.ALTAIR_FORK_EPOCH.toNat) :
    upgradeDue config (⟨.phase0, state⟩ : ForkedBeaconState preset) = false := by
  simp only [upgradeDue, Config.nextFork, Option.any_some, Bool.and_eq_false_iff,
    beq_eq_false_iff_ne]
  refine .inr fun same => ?_
  have epoch : (computeEpochAtSlot preset state.slot).toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div]
  rw [same] at epoch
  omega

/-- The caching of a slot keeps the absence of signers. -/
private theorem Quiet.of_processSlot {state cached : BeaconState preset fork}
    (quiet : Quiet state) (computed : processSlot state = .ok cached) : Quiet cached := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact quiet

/-- A run before the Altair fork epoch stays at Phase 0 and moves the slot by its length.

It also keeps the absence of signers. -/
private theorem advanceSlotsAcross_quiet : ∀ (steps : Nat) {state : BeaconState preset .phase0}
    {reached : ForkedBeaconState preset}, Quiet state →
    (state.slot.toNat + steps) / preset.SLOTS_PER_EPOCH.toNat < config.ALTAIR_FORK_EPOCH.toNat →
    advanceSlotsAcross config checks steps ⟨.phase0, state⟩ = .ok reached →
    ∃ ended : BeaconState preset .phase0, reached = ⟨.phase0, ended⟩ ∧
      ended.slot.toNat = state.slot.toNat + steps ∧ Quiet ended
  | 0, state, reached, quiet, _, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    exact ⟨state, computed.symm, rfl, quiet⟩
  | steps + 1, state, reached, quiet, before, computed => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp nextOk
    have slot : advanced.slot.toNat = state.slot.toNat + 1 := advanceSlot_slot advancedOk
    -- The next slot is still before the fork epoch, so no upgrade runs.
    have notDue : upgradeDue config (⟨.phase0, advanced⟩ : ForkedBeaconState preset) = false :=
      upgradeDue_phase0 (Nat.lt_of_le_of_lt (Nat.div_le_div_right (by omega)) before)
    rw [processUpgrades_of_not_due notDue, Except.ok.injEq] at upgraded
    subst upgraded
    obtain ⟨ended, same, endedSlot, endedQuiet⟩ := advanceSlotsAcross_quiet steps
      (Quiet.of_advanceSlot quiet advancedOk)
      (by rwa [slot, Nat.add_right_comm, Nat.add_assoc]) rest
    exact ⟨ended, same, by omega, endedQuiet⟩

/-- A run that stays before Altair, from a state where no one has signed, meets all three.

It meets the draws in their form at the cap, which gives the end of each draw.

No one signs in the run, so the signers hold at most the total active balance.

An epoch before Altair draws nothing, and no upgrade is due before the Altair fork epoch.

The run ends at an epoch within the limit before Altair. -/
theorem runHypotheses_of_quiet {state : BeaconState preset .phase0} {count : Nat}
    (quiet : Quiet state)
    (before : (state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat <
      config.ALTAIR_FORK_EPOCH.toNat)
    (limit : (state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤
      preset.epochLimitBeforeAltair) :
    SignersEarly config checks ⟨.phase0, state⟩ count ∧
      DrawsAtCap config checks ⟨.phase0, state⟩ count ∧
      EpochLimitBeforeAltair (preset := preset) ⟨.phase0, state⟩ count := by
  -- Every slot the run reaches before its end stays before the fork epoch.
  have early : ∀ {slot}, slot ≤ state.slot.toNat + count →
      slot / preset.SLOTS_PER_EPOCH.toNat < config.ALTAIR_FORK_EPOCH.toNat :=
    fun within => Nat.lt_of_le_of_lt (Nat.div_le_div_right within) before
  refine ⟨?_, ?_, ?_⟩
  · intro steps short reached computed _ _ cached cachedOk
    obtain ⟨ended, rfl, -, endedQuiet⟩ :=
      advanceSlotsAcross_quiet steps quiet (early (by omega)) computed
    exact (endedQuiet.of_processSlot cachedOk).signers
  · intro steps short reached computed
    obtain ⟨ended, rfl, endedSlot, -⟩ :=
      advanceSlotsAcross_quiet steps quiet (early (by omega)) computed
    -- At Phase 0 an epoch draws nothing.
    refine ⟨fun _ _ _ => ⟨fun altair => absurd altair (by decide : ¬ Fork.altair ≤ .phase0),
      fun altair => absurd altair (by decide : ¬ Fork.altair ≤ .phase0),
      fun fulu => absurd fulu (by decide : ¬ Fork.fusaka ≤ .phase0),
      fun gloas => absurd gloas (by decide : ¬ Fork.glamsterdam ≤ .phase0)⟩, ?_⟩
    intro advanced advancedOk upgrading passes due
    have slot : advanced.slot.toNat = ended.slot.toNat + 1 := advanceSlot_slot advancedOk
    have notDue : upgradeDue config (⟨.phase0, advanced⟩ : ForkedBeaconState preset) = false :=
      upgradeDue_phase0 (early (by omega))
    -- With no upgrade due, the upgrades pass through the state alone.
    cases passes with
    | refl => exact (Bool.false_ne_true (notDue.symm.trans due)).elim
    | step stepDue => exact (Bool.false_ne_true (notDue.symm.trans stepDue)).elim
  · exact fun _ => limit

/-- The empty state at genesis, before any deposit, is quiet. -/
theorem emptyGenesisState_quiet (before : fork < .altair) (genesisTime : UInt64)
    (eth1BlockHash : Hash32) (depositCount : UInt64) (bodyRoot : Root) :
    Quiet (emptyGenesisState (preset := preset) config before genesisTime eth1BlockHash
      depositCount bodyRoot) := by
  -- Both lists of attestations are empty, and no participation exists before Altair.
  have never : ¬ .altair ≤ fork := fun altair => absurd (Nat.lt_of_lt_of_le before altair) (by simp)
  exact ⟨⟨fun _ => rfl, fun altair => absurd altair never⟩, fun _ => rfl,
    fun altair => absurd altair never⟩

/-- On mainnet, a run from a quiet state before Altair meets all three, up to the Altair fork.

It meets the draws in their form at the cap. -/
theorem runHypotheses_mainnet {state : BeaconState Preset.mainnet .phase0} {count : Nat}
    (quiet : Quiet state)
    (before : (state.slot.toNat + count) / 32 < 74240) :
    SignersEarly Config.mainnet checks ⟨.phase0, state⟩ count ∧
      DrawsAtCap Config.mainnet checks ⟨.phase0, state⟩ count ∧
      EpochLimitBeforeAltair (preset := Preset.mainnet) ⟨.phase0, state⟩ count := by
  have epochLength : Preset.mainnet.SLOTS_PER_EPOCH.toNat = 32 := rfl
  have altair : Config.mainnet.ALTAIR_FORK_EPOCH.toNat = 74240 := rfl
  have limit := Preset.epochLimitBeforeAltair_mainnet
  exact runHypotheses_of_quiet quiet (by rw [epochLength, altair]; exact before)
    (by rw [epochLength]; omega)

end EthLib.Consensus
