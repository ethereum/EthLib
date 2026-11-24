module

public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Proofs.Transition.BalanceDrift

/-!
# Proofs: when slashing one validator succeeds

Slashing a validator starts its exit, marks it slashed and adds to the slashed balance of the epoch.

It then debits the validator a first penalty and credits the whistleblower reward.

Each of those steps can fail on checked arithmetic or on a read outside the registry.

The room here excludes each failure, with the proposer as whistleblower.

It is enough for slashing to succeed; it is not the least room that slashing needs.

The slashings of a block before an attester slashing keep the frame, activity and the proposer.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- The room a state has for slashing one validator, with the proposer as whistleblower.

Starting the validator's exit succeeds.

The epoch has room for the slashings vector, whose length is nonzero.

The slashed balance of the epoch has room for the effective balance of the validator.

From Altair, the whistleblower reward times the proposer weight fits in 64 bits.

The proposer lookup succeeds.

The balance of the proposer has room for that effective balance.

The validator has a balance. -/
structure SlashRoom (config : Config) (state : BeaconState preset fork) (validator : Validator)
    (index : ValidatorIndex) : Prop where
  /-- Starting the validator's exit succeeds. -/
  exit : ∃ exited, initiateValidatorExit config state index = .ok exited
  /-- The epoch has room for the slashings vector. -/
  window : (getCurrentEpoch state).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat < 2 ^ 64
  /-- The slashings vector has a nonzero length. -/
  vector : preset.EPOCHS_PER_SLASHINGS_VECTOR ≠ 0
  /-- The slashed balance of the epoch has room for the effective balance. -/
  slashed : ∀ amount, readCircular state.slashings.elements (getCurrentEpoch state) = .ok amount →
    amount.toNat + validator.effectiveBalance.toNat < 2 ^ 64
  /-- From Altair, the reward times the proposer weight fits in 64 bits. -/
  reward : .altair ≤ fork → (validator.effectiveBalance /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat * PROPOSER_WEIGHT.toNat < 2 ^ 64
  /-- The proposer lookup succeeds, and its balance has room for the effective balance. -/
  proposer : ∃ p b, getBeaconProposerIndex state = .ok p ∧ getBalance state p = .ok b ∧
    b.toNat + validator.effectiveBalance.toNat < 2 ^ 64
  /-- The validator has a balance. -/
  balance : ∃ b, getBalance state index = .ok b

/-- Slashing a validator, with the proposer as whistleblower, succeeds on a state with room. -/
theorem slashValidator_total_of_room {config : Config} {state : BeaconState preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (room : SlashRoom config state validator index) :
    ∃ after, slashValidator config state index = .ok after := by
  have : NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat :=
    ⟨fun zero => room.vector (UInt64.toNat_inj.mp (by simpa using zero))⟩
  -- The exit keeps the balances, the slashed balances and the effective balance.
  obtain ⟨exited, exitOk⟩ := room.exit
  obtain ⟨exitBalances, -, -, current, currentOk, sameEffective⟩ :=
    effectiveBalance_initiateValidatorExit found exitOk
  have exitSlashings := slashings_initiateValidatorExit exitOk
  have inside : index.toNat < exited.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp currentOk)).1
  -- The withdrawable epoch fits, and the mark is written inside the registry.
  have windowOk := addChecked_of_lt room.window
  let marked := exited.putValidator index.toNat inside
    { current with
      slashed := true
      withdrawableEpoch := max current.withdrawableEpoch
        (getCurrentEpoch state + preset.EPOCHS_PER_SLASHINGS_VECTOR) }
  have markedOk : exited.setValidator index
      { current with
        slashed := true
        withdrawableEpoch := max current.withdrawableEpoch
          (getCurrentEpoch state + preset.EPOCHS_PER_SLASHINGS_VECTOR) } = .ok marked := by
    simp [BeaconState.setValidator, inside, marked]
  -- The slashed balance of the epoch has room for the effective balance.
  obtain ⟨amount, amountOk⟩ := readCircular_total state.slashings.elements (getCurrentEpoch state)
  have amountOk' : readCircular marked.slashings.elements (getCurrentEpoch state) = .ok amount := by
    simpa [marked, BeaconState.putValidator, exitSlashings] using amountOk
  have totalOk := addChecked_of_lt (sameEffective ▸ room.slashed amount amountOk)
  obtain ⟨slashings, slashingsOk⟩ := writeCircularRooted_total marked.slashings
    (getCurrentEpoch state) (amount + current.effectiveBalance)
  -- The debit reads the balance of the validator, which the exit and the mark keep.
  obtain ⟨balance, balanceOk⟩ := room.balance
  have balancesSame : ({ marked with slashings } : BeaconState preset fork).balances =
      state.balances := by
    simpa [marked, BeaconState.putValidator] using exitBalances
  have balanceInside :
      index.toNat < ({ marked with slashings } : BeaconState preset fork).balances.data.size := by
    rw [balancesSame]
    exact (Array.getElem?_eq_some_iff.mp (getBalance_eq_ok_iff.mp balanceOk)).1
  let penalty := current.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT
  let lowered := ({ marked with slashings } : BeaconState preset fork).putBalance index.toNat
    balanceInside (saturatingSub
      ({ marked with slashings } : BeaconState preset fork).balances.data[index.toNat] penalty)
  have loweredOk : decreaseBalance { marked with slashings } index penalty = .ok lowered :=
    decreaseBalance_eq_ok_iff.mpr ⟨balanceInside, rfl⟩
  -- The proposer of the debited state is the proposer of the state.
  obtain ⟨proposer, proposerBalance, proposerOk, proposerBalanceOk, proposerRoom⟩ := room.proposer
  have proposerLowered : getBeaconProposerIndex lowered = .ok proposer := by
    rw [getBeaconProposerIndex_slashDebit (StepKeeps.refl state) (PayloadInputs.refl state)
      (effectiveKept_refl state) exitOk currentOk markedOk loweredOk]
    exact proposerOk
  -- The proposer's share is at most the reward, which is at most the effective balance.
  let reward := current.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT
  have rewardLe : reward.toNat ≤ validator.effectiveBalance.toNat := by
    rw [← sameEffective, UInt64.toNat_div]
    exact Nat.div_le_self _ _
  obtain ⟨share, shareOk⟩ : ∃ share, proposerShare preset fork reward = .ok share := by
    unfold proposerShare
    split
    · rename_i altair
      have fits : reward.toNat * PROPOSER_WEIGHT.toNat < 2 ^ 64 := by
        simpa only [reward, sameEffective] using room.reward altair
      simp only [liftArith, mulChecked_of_lt fits, bind, Except.bind, pure, Except.pure,
        Except.mapError]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have shareLe := proposerShare_le shareOk
  -- The proposer's balance after the debit is at most its balance in the state.
  have loweredBalances : lowered.balances.data.size = state.balances.data.size := by
    have := congrArg (fun balances => balances.data.size) balancesSame
    simpa [lowered, BeaconState.putBalance] using this
  have proposerRead := getBalance_eq_ok_iff.mp proposerBalanceOk
  have proposerInside : proposer.toNat < lowered.balances.data.size := by
    rw [loweredBalances]
    exact (Array.getElem?_eq_some_iff.mp proposerRead).1
  have lowerLe : ∀ j (hj : j < lowered.balances.data.size),
      (lowered.balances.data[j]'hj).toNat ≤
        (state.balances.data[j]'(loweredBalances ▸ hj)).toNat := by
    intro j hj
    have markedBalances : marked.balances = state.balances := balancesSame
    simp only [lowered, BeaconState.putBalance, Array.getElem_set]
    split
    · rename_i same
      subst same
      simp only [toNat_saturatingSub]
      have read : marked.balances.data[index.toNat]'(by simpa using balanceInside) =
          state.balances.data[index.toNat]'(loweredBalances ▸ hj) := by
        simp only [markedBalances]
      rw [read]
      omega
    · have read : marked.balances.data[j]'(by simpa [lowered, BeaconState.putBalance] using hj) =
          state.balances.data[j]'(loweredBalances ▸ hj) := by
        simp only [markedBalances]
      rw [read]
      exact Nat.le_refl _
  have proposerBound : proposer.toNat < state.balances.data.size := by
    rw [← loweredBalances]
    exact proposerInside
  have proposerAt : state.balances.data[proposer.toNat]'proposerBound = proposerBalance := by
    rw [Array.getElem?_eq_getElem proposerBound] at proposerRead
    exact Option.some.inj proposerRead
  have debited : (lowered.balances.data[proposer.toNat]'proposerInside).toNat ≤
      proposerBalance.toNat := proposerAt ▸ lowerLe _ proposerInside
  -- Both credits go to the proposer and sum to the reward.
  let raised := lowered.putBalance proposer.toNat proposerInside
    (lowered.balances.data[proposer.toNat] + share)
  have firstFits : (lowered.balances.data[proposer.toNat]'proposerInside).toNat + share.toNat <
      2 ^ 64 := by
    omega
  have raisedOk : increaseBalance lowered proposer share = .ok raised :=
    increaseBalance_eq_ok_iff.mpr ⟨proposerInside, firstFits, rfl⟩
  have raisedInside : proposer.toNat < raised.balances.data.size := by
    simpa [raised, BeaconState.putBalance] using proposerInside
  have raisedAt : (raised.balances.data[proposer.toNat]'raisedInside) =
      lowered.balances.data[proposer.toNat] + share := by
    simp [raised, BeaconState.putBalance]
  have leftEq : (reward - share).toNat = reward.toNat - share.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe)
  have secondFits : (raised.balances.data[proposer.toNat]'raisedInside).toNat +
      (reward - share).toNat < 2 ^ 64 := by
    rw [raisedAt, toNat_add_of_lt firstFits, leftEq]
    omega
  obtain ⟨last, lastOk⟩ : ∃ last, increaseBalance raised proposer (reward - share) = .ok last :=
    ⟨_, increaseBalance_eq_ok_iff.mpr ⟨raisedInside, secondFits, rfl⟩⟩
  refine ⟨if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index else last, ?_⟩
  simp only [slashValidator, exitOk, currentOk, liftArith, windowOk, markedOk, amountOk',
    totalOk, slashingsOk, loweredOk, proposerLowered, shareOk, raisedOk, Option.getD_none, lastOk,
    bind, Except.bind, pure, Except.pure, Except.mapError, penalty, reward]

/-- The steps from the operations of a block to the turn of an attester slashing keep three things.

They keep the frame, activity and the proposer read, which may fail on both states.

The turn is the state that the steps before that attester slashing reach. -/
theorem slashingTurn_kept {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {state turn : BeaconState preset fork}
    {block : BeaconBlock preset fork} {j : Nat}
    (turned : SlashingTurn config checks engine state block j turn) :
    ∃ input, OperationsInput config checks engine state block input ∧ Frame input turn ∧
      StepKeeps input turn ∧ getBeaconProposerIndex turn = getBeaconProposerIndex input := by
  obtain ⟨input, proposed, started, proposersOk, attestersOk⟩ := turned
  rw [← Array.foldlM_toList] at proposersOk
  -- Each slashing keeps the frame, the payload inputs, activity and the effective balances.
  let Keeps (a b : BeaconState preset fork) : Prop :=
    Frame a b ∧ PayloadInputs a b ∧ StepKeeps a b ∧ EffectiveKept a b
  have trans {a b c : BeaconState preset fork} (one : Keeps a b) (two : Keeps b c) : Keeps a c :=
    ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.1.trans two.2.2.1,
      effectiveKept_trans one.2.2.2 two.2.2.2 one.2.2.1.1⟩
  have proposedKeeps : Keeps input proposed :=
    foldlM_ok_invariant (Keeps input) (fun _ _ _ before ok => trans before
      ⟨(frame_processProposerSlashing ok).toFrame, payloadInputs_processProposerSlashing ok,
        stepKeeps_processProposerSlashing ok, effectiveKept_proposerSlashing ok⟩)
      ⟨Frame.refl input, PayloadInputs.refl input, StepKeeps.refl input, effectiveKept_refl input⟩
      proposersOk
  have turnKeeps : Keeps input turn :=
    foldlM_ok_invariant (Keeps input) (fun _ _ _ before ok => trans before
      ⟨(frame_processAttesterSlashing ok).toFrame, payloadInputs_processAttesterSlashing ok,
        stepKeeps_processAttesterSlashing ok, effectiveKept_attesterSlashing ok⟩)
      proposedKeeps attestersOk
  -- Those four things fix the proposer.
  exact ⟨input, started, turnKeeps.1, turnKeeps.2.2.1,
    getBeaconProposerIndex_of_kept turnKeeps.2.2.1 turnKeeps.2.1 turnKeeps.2.2.2⟩

end EthLib.Consensus
