module

public import EthLib.Consensus.Proofs.HonestAttestations
public import EthLib.Consensus.Proofs.HonestSlotAggregate
import EthLib.Base.Proofs.Forall2
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept

/-!
# Proofs: the attestation steps accept a list of honest attestations, and flag honest members

From Altair until Gloas, the attestation steps of a block accept a list of honest attestations.

From Electra the same holds for a list of honest aggregates, each covering one slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {state : BeaconState preset fork}

/-- Writing one entry of a list raises a sum read in step with it by at most a bound.

The new term at that entry must be at most the old term plus that bound. -/
private theorem sum_zipWith_set_le {α β : Type} (f : α → β → Nat) (value : β) (raise : Nat) :
    ∀ (first : List α) (second : List β) (index : Nat),
      (∀ a (inside : index < second.length), f a value ≤ f a second[index] + raise) →
      (first.zipWith f (second.set index value)).sum ≤ (first.zipWith f second).sum + raise
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: _, _ :: _, 0, bounded => by
    have := bounded a (by simp)
    simp only [List.set_cons_zero, List.zipWith_cons_cons, List.sum_cons,
      List.getElem_cons_zero] at this ⊢
    omega
  | _ :: first, _ :: second, index + 1, bounded => by
    have := sum_zipWith_set_le f value raise first second index fun a inside =>
      bounded a (by simpa using inside)
    simp only [List.set_cons_succ, List.zipWith_cons_cons, List.sum_cons]
    omega

/-- Raising one balance raises the stake sum by at most the raise. -/
private theorem stakeSum_increaseBalance_le {after : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    stakeSum after ≤ stakeSum state + delta.toNat := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  unfold stakeSum
  simp only [BeaconState.putBalance, Array.toList_set]
  refine sum_zipWith_set_le _ _ _ _ _ _ fun validator _ => ?_
  rw [Uint64.toNat_add_of_lt fits]
  simp only [Array.getElem_toList]
  omega

/-- Writing flags and then raising one balance keeps the bounds, with the raise added. -/
private theorem withinBudget_raise {budget scoreBound raised : Nat}
    {after : BeaconState preset fork} {current : Bool} {updated : EpochParticipation preset fork}
    {proposer : ValidatorIndex} {reward : Gwei} (holds : WithinBudget budget scoreBound state)
    (computed : increaseBalance (setEpochParticipation state current updated) proposer reward =
      .ok after)
    (enough : budget + reward.toNat ≤ raised) :
    WithinBudget raised scoreBound after := by
  obtain ⟨inside, -, written⟩ := increaseBalance_eq_ok_iff.mp computed
  have summed := stakeSum_increaseBalance_le computed
  have sameStake : stakeSum (setEpochParticipation state current updated) = stakeSum state := by
    cases current <;> rfl
  have samePending : pendingDepositSum after = pendingDepositSum state := by
    subst written
    cases current <;> rfl
  have sameSlashed : slashedBalanceSum after = slashedBalanceSum state := by
    subst written
    cases current <;> rfl
  have funded := holds.funded
  have slashed := holds.slashed
  have matched : BalancesMatch state := holds.matched
  subst written
  cases current <;>
  · refine ⟨holds.within, ?_, holds.capped, by omega, by omega, holds.scored, fun electra =>
      ⟨Nat.le_trans (holds.carried electra).1 (by omega),
        Nat.le_trans (holds.carried electra).2 (by omega)⟩⟩
    simpa [BalancesMatch, BeaconState.putBalance, setEpochParticipation] using matched

/-- Writing flags and then raising one balance changes only the balances and the flags. -/
private theorem shaped_raise {other after : BeaconState preset fork} {current : Bool}
    {updated : EpochParticipation preset fork} {proposer : ValidatorIndex} {reward : Gwei}
    (shaped : ∃ balances previous current, other = { state with
      balances := balances, previousEpochParticipation := previous,
      currentEpochParticipation := current })
    (computed : increaseBalance (setEpochParticipation other current updated) proposer reward =
      .ok after) :
    ∃ balances previous current, after = { state with
      balances := balances, previousEpochParticipation := previous,
      currentEpochParticipation := current } := by
  obtain ⟨balances, previous, current', rfl⟩ := shaped
  obtain ⟨inside, -, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  cases current
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

/-- Writing flags of the size of the registry and raising one balance keeps the sizes of flags. -/
private theorem participationMatches_raise {after : BeaconState preset fork} {current : Bool}
    {updated : EpochParticipation preset fork} {proposer : ValidatorIndex} {reward : Gwei}
    (participation : ParticipationMatches state)
    (sized : updated.data.size = state.validators.data.size)
    (computed : increaseBalance (setEpochParticipation state current updated) proposer reward =
      .ok after) :
    ParticipationMatches after := by
  obtain ⟨inside, -, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  intro altair
  obtain ⟨previous, current'⟩ := participation altair
  cases current
  · exact ⟨sized, current'⟩
  · exact ⟨previous, sized⟩

/-- From Altair, a list of attestations keeps each target flag. -/
private theorem foldlM_processAttestation_targetFlag {checks : SignatureChecks}
    {parentSlot : Slot} (altair : .altair ≤ fork) (current : Bool) (position : Nat)
    {attestations : List (Attestation preset fork)} {first last : BeaconState preset fork}
    (computed :
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok last)
    (flagged : TargetFlagAt (recentParticipation first altair current) position) :
    TargetFlagAt (recentParticipation last altair current) position :=
  targetFlagAt_iff.mpr (foldlM_ok_invariant
    (fun now : BeaconState preset fork => hasFlag
      (((recentParticipation now altair current).data[position]?).getD 0)
      (⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length).val.toUInt64 = true)
    (fun _ _ _ held ok => processAttestation_keepsFlag ok altair current position _ held)
    (targetFlagAt_iff.mp flagged) computed)

/-- An attestation step from Altair until Gloas writes flags, then raises one balance. -/
private theorem processAttestation_raise {budget scoreBound : Nat} {checks : SignatureChecks}
    {after : BeaconState preset fork} {attestation : Attestation preset fork} {parentSlot : Slot}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    (fits : preset.baseRewardCeiling < 2 ^ 64)
    (room : budget + state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ current updated proposer reward,
      increaseBalance (setEpochParticipation state current updated) proposer reward = .ok after ∧
      updated.data.size = state.validators.data.size ∧
      reward.toNat ≤ state.validators.data.size * (64 * preset.baseRewardCeiling) / 448 := by
  rw [processAttestation_of_altair altair] at computed
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, -, indexed, indexedOk, valid, validOk, _,
    validTrue, total, totalOk, attesters, attestersOk, ⟨updated, numerator⟩, folded, proposer, -,
    raised, raisedOk, final⟩ := computed
  split at final
  · rename_i gloas
    exact absurd beforeGloas (Nat.not_lt_of_le gloas)
  cases final
  obtain rfl : valid = true := ensure_ok_iff.mp validTrue
  obtain ⟨named, namedOk, indices⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
  rw [attestersOk, Except.ok.injEq] at namedOk
  subst namedOk
  -- The attesters are distinct validators of the registry, so there are at most that many.
  have inside : ∀ attester ∈ attesters, attester.toNat < state.validators.data.size :=
    fun attester member =>
      isValidIndexedAttestation_lt_size validOk attester (by rw [indices]; simpa using member)
  have counted := Nat.mul_le_mul_right (64 * preset.baseRewardCeiling)
    (length_le_of_toNat_nodup (getAttestingIndices_nodup attestersOk) inside)
  -- The total active balance is the one that the budget bounds, so each base reward is small.
  obtain ⟨other, otherOk, low, -⟩ := getTotalActiveBalance_exists_ok holds.within
    (Nat.lt_of_le_of_lt holds.effectiveBalanceSum_le (by omega))
  rw [totalOk, Except.ok.injEq] at otherOk
  subst otherOk
  have baseOk := getBaseReward_exists_le altair holds increment scaled fits low
  obtain ⟨previousSize, currentSize⟩ := participation altair
  have sized : (if (attestation.data.target.epoch == getCurrentEpoch state) = true then
      state.currentEpochParticipation altair
    else state.previousEpochParticipation altair).data.size = state.validators.data.size := by
    split <;> assumption
  obtain ⟨updated', numerator', folded', numeratorLe⟩ :=
    foldlM_addAttesterFlags_exists_ok (earned := earned) baseOk attesters _ 0 sized inside
      (by simp only [UInt64.toNat_zero]; omega)
  rw [folded, Except.ok.injEq, Prod.mk.injEq] at folded'
  obtain ⟨rfl, rfl⟩ := folded'
  refine ⟨_, updated, proposer, _, raisedOk, ?_, ?_⟩
  · exact foldlM_ok_invariant
      (fun (carried : EpochParticipation preset fork × Gwei) =>
        carried.1.data.size = state.validators.data.size)
      (fun ⟨_, _⟩ _ ⟨_, _⟩ holds ok => (addAttesterFlags_keeps ok).1.trans holds) sized folded
  · -- The reward is the numerator over 448, and the numerator is at most the bound.
    have denominator : ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
        PROPOSER_WEIGHT).toNat = 448 := by decide
    dsimp only
    rw [UInt64.toNat_div, denominator]
    exact Nat.div_le_div_right (by simp only [UInt64.toNat_zero] at numeratorLe; omega)

/-- One attestation step of a list, from Altair until Gloas, spends one reward share of the budget.

The state it reaches keeps the registry, the flag sizes and the budget with one more share.

If the state before differs from the first only in balances and flags, so does the state after.

The budget must leave room for the shares of the rest of the list. -/
private theorem processAttestation_budgetStep {budget scoreBound spent rest : Nat}
    {checks : SignatureChecks} {parentSlot : Slot} {attestation : Attestation preset fork}
    {first middle : BeaconState preset fork} (altair : .altair ≤ fork)
    (beforeGloas : fork < .glamsterdam) (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (positive : 0 < state.validators.data.size) (validators : first.validators = state.validators)
    (holds : WithinBudget (budget + spent * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448)) scoreBound first)
    (participation : ParticipationMatches first)
    (room : budget + (spent + (rest + 1)) * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (processed : processAttestation config checks first parentSlot attestation = .ok middle) :
    middle.validators = state.validators ∧
      WithinBudget (budget + (spent + 1) * (state.validators.data.size *
        (64 * preset.baseRewardCeiling) / 448)) scoreBound middle ∧
      ParticipationMatches middle ∧
      ((∃ balances previous current, first = { state with
        balances := balances, previousEpochParticipation := previous,
        currentEpochParticipation := current }) →
        ∃ balances previous current, middle = { state with
          balances := balances, previousEpochParticipation := previous,
          currentEpochParticipation := current }) := by
  have ceilingLe : 64 * preset.baseRewardCeiling ≤
      state.validators.data.size * (64 * preset.baseRewardCeiling) :=
    Nat.le_mul_of_pos_left _ positive
  have spentLe : spent * (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) ≤
      (spent + (rest + 1)) * (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) :=
    Nat.mul_le_mul_right _ (by omega)
  -- The step writes flags and pays the proposer one share at most.
  obtain ⟨written, updated, payee, reward, raised, sized, rewardLe⟩ :=
    processAttestation_raise altair beforeGloas increment scaled holds participation
      (by omega) (by rw [validators]; omega) processed
  rw [validators] at rewardLe
  have shareStep : (spent + 1) *
      (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) =
      spent * (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) / 448 :=
    Nat.succ_mul _ _
  have middleValidators : middle.validators = state.validators := by
    obtain ⟨_, -, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    cases written <;> exact validators
  exact ⟨middleValidators, withinBudget_raise holds raised (by omega),
    participationMatches_raise participation sized raised, fun shaped => shaped_raise shaped raised⟩

/-- The attestation steps from a state that differs from the first only in balances and flags.

Each attestation of the list passes on every such state within a budget with room for one reward.

It then flags the validators that it marks, in the flags of its epoch.

Each step of the list may spend one reward share of the budget. -/
private theorem foldlM_processAttestation_of_accepted_from {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (positive : 0 < state.validators.data.size) {parentSlot : Slot} {ι : Type}
    (marked : ι → ValidatorIndex → Prop) (isCurrent : ι → Bool)
    {items : List ι} {attestations : List (Attestation preset fork)}
    (accepted : List.Forall₂ (fun item attestation =>
      ∀ (funds : Nat) (first : BeaconState preset fork),
        (∃ balances previous current, first = { state with
          balances := balances, previousEpochParticipation := previous,
          currentEpochParticipation := current }) →
        WithinBudget funds scoreBound first → ParticipationMatches first →
        funds + state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64 →
        ∃ middle, processAttestation config .bls first parentSlot attestation = .ok middle ∧
          ∀ index, marked item index →
            TargetFlagAt (recentParticipation middle altair (isCurrent item)) index.toNat)
      items attestations)
    (first : BeaconState preset fork) (spent : Nat)
    (shaped : ∃ balances previous current, first = { state with
      balances := balances, previousEpochParticipation := previous,
      currentEpochParticipation := current })
    (holds : WithinBudget (budget + spent * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448)) scoreBound first)
    (participation : ParticipationMatches first)
    (room : budget + (spent + items.length) * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64) :
    ∃ after, attestations.foldlM (processAttestation config .bls · parentSlot ·) first = .ok after ∧
      ∀ item ∈ items, ∀ index, marked item index →
        TargetFlagAt (recentParticipation after altair (isCurrent item)) index.toNat := by
  induction accepted generalizing first spent with
  | nil => exact ⟨first, rfl, fun item member => absurd member List.not_mem_nil⟩
  | @cons item attestation items attestations head tail ih =>
    rw [List.length_cons] at room
    have spentLe : spent * (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) ≤
        (spent + (items.length + 1)) *
          (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) :=
      Nat.mul_le_mul_right _ (by omega)
    -- The first attestation passes on the state the list starts from.
    obtain ⟨middle, processed, flagged⟩ := head _ first shaped holds participation (by omega)
    have firstValidators : first.validators = state.validators := by
      obtain ⟨_, _, _, rfl⟩ := shaped
      rfl
    -- The step spends one share of the budget, and the rest of the list runs on its state.
    obtain ⟨-, raisedHolds, raisedParticipation, raisedShape⟩ :=
      processAttestation_budgetStep altair beforeGloas increment scaled positive firstValidators
        holds participation room processed
    obtain ⟨after, folded, rest⟩ := ih middle (spent + 1) (raisedShape shaped) raisedHolds
      raisedParticipation
      (by rw [show spent + 1 + items.length = spent + (items.length + 1) by omega]; exact room)
    refine ⟨after, by rw [List.foldlM_cons, processed]; exact folded, ?_⟩
    intro other member index chosen
    rcases List.mem_cons.mp member with rfl | member
    · -- The first attestation flags what it marks, and the later steps keep the flags.
      exact foldlM_processAttestation_targetFlag altair _ _ folded (flagged index chosen)
    · exact rest other member index chosen

/-- From Altair until Gloas, the attestation steps accept the honest attestations of committees.

Each vote names its data and its committee, and its attestation is built from the state.

The data and the state meet the checks of the attestation step, and the state is within a budget.

The budget must leave room for the rewards of the proposer, one for each attestation of the list.

Each honest member of each committee then holds the timely target flag of its target epoch.

That needs the state to hold the target root for the first slot of that epoch. -/
theorem foldlM_processAttestation_honestAttestation {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (parentSlot : Slot) (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    {votes : List (AttestationData × CommitteeIndex)}
    -- Each reward is at most 64 base reward ceilings for each validator of the registry, over 448.
    --
    -- The budget must also leave room for that bound before the division.
    (room : budget + votes.length * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (recent : ∀ vote ∈ votes, vote.1.target.epoch = getPreviousEpoch state ∨
      vote.1.target.epoch = getCurrentEpoch state)
    (slotEpoch : ∀ vote ∈ votes, vote.1.target.epoch = computeEpochAtSlot preset vote.1.slot)
    (past : ∀ vote ∈ votes, vote.1.slot.toNat < state.slot.toNat)
    (early : ∀ vote ∈ votes,
      vote.1.slot.toNat + preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤ state.slot.toNat)
    (deadline : ∀ vote ∈ votes, fork < .dencun →
      state.slot.toNat ≤ vote.1.slot.toNat + preset.SLOTS_PER_EPOCH.toNat)
    (indexed : ∀ vote ∈ votes, vote.1.index = if .pectra ≤ fork then 0 else vote.2)
    (below : ∀ vote ∈ votes, vote.2 < getCommitteeCountPerSlot state vote.1.target.epoch)
    (source : ∀ vote ∈ votes, vote.1.source =
      if vote.1.target.epoch = getCurrentEpoch state then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint)
    (registered : ∀ index ∈ honest, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : ∀ vote ∈ votes, ∀ committee,
      getBeaconCommittee state vote.1.slot vote.2 = .ok committee →
        (((honestSigners honest committee).map key).map (·.val)).sum ≠ 0)
    (proposer : ∃ index, getBeaconProposerIndex state = .ok index ∧
      index.toNat < state.validators.data.size)
    {attestations : List (Attestation preset fork)}
    (built : List.Forall₂ (fun vote attestation =>
      honestAttestation config state honest key vote.1 vote.2 = .ok attestation)
        votes attestations) :
    ∃ after, attestations.foldlM (processAttestation config .bls · parentSlot ·) state = .ok after ∧
      ∀ vote ∈ votes, getBlockRoot state vote.1.target.epoch = .ok vote.1.target.root →
        ∀ committee, getBeaconCommittee state vote.1.slot vote.2 = .ok committee →
          ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation after altair
            (vote.1.target.epoch == getCurrentEpoch state)) index.toNat := by
  -- The registry has a validator, so the ceiling of a base reward fits.
  have positive : 0 < state.validators.data.size := by
    obtain ⟨index, -, inside⟩ := proposer
    omega
  -- A block runs its attestations one after the other, each on the state that the one before left.
  --
  -- Each attestation pays the proposer a reward, which the budget must leave room for.
  --
  -- Each attestation passes on every state like the first, which has spent no budget.
  obtain ⟨after, folded, flagged⟩ := foldlM_processAttestation_of_accepted_from altair beforeGloas
    increment scaled positive
    (fun (vote : AttestationData × CommitteeIndex) index =>
      getBlockRoot state vote.1.target.epoch = .ok vote.1.target.root ∧
      ∃ committee, getBeaconCommittee state vote.1.slot vote.2 = .ok committee ∧
        index ∈ committee ∧ index ∈ honest)
    (fun vote => vote.1.target.epoch == getCurrentEpoch state)
    (((List.forall₂_and_left _ _).mpr
      ⟨fun vote member => And.intro (recent vote member) (And.intro (slotEpoch vote member)
        (And.intro (past vote member) (And.intro (early vote member)
          (And.intro (deadline vote member) (And.intro (indexed vote member) (And.intro
            (below vote member) (And.intro (source vote member) (sum vote member)))))))),
        built⟩).imp
      fun vote attestation ⟨⟨recent, slotEpoch, past, early, deadline, indexed, below, source, sum⟩,
        head⟩ funds first shaped holds participation room => by
      -- The committee of the vote has a value, since its honest attestation reads it.
      obtain ⟨committee, committeeOk⟩ :
          ∃ committee, getBeaconCommittee state vote.1.slot vote.2 = .ok committee := by
        have read := head
        unfold honestAttestation at read
        split at read
        · obtain ⟨committee, found, -⟩ := bind_ok_iff.mp read
          exact ⟨committee, mapError_ok_iff.mp found⟩
        · rename_i electra
          obtain ⟨committee, found, -⟩ := bind_ok_iff.mp read
          rw [indexed, ite_eq_right electra] at found
          exact ⟨committee, mapError_ok_iff.mp found⟩
      -- An attestation changes only the flags of its attesters and the balance of the proposer.
      --
      -- So the next attestation reads the same committees, checkpoints, roots and keys.
      obtain ⟨balances, previous, current, rfl⟩ := shaped
      -- Its honest attestation is the same on each such state, since it reads only those values.
      --
      -- The step reads only what the first state holds, so the honest attestation is accepted.
      obtain ⟨middle, processed, flagged⟩ := processAttestation_honestAttestation
        (state := { state with
          balances := balances, previousEpochParticipation := previous,
          currentEpochParticipation := current }) altair beforeGloas parentSlot roots slotRoom
        increment scaled holds participation room recent slotEpoch past early deadline indexed
        below committeeOk source
        (fun index signer => registered index (mem_honestSigners.mp signer).2)
        (sum committee committeeOk) proposer head
      refine ⟨middle, processed, fun index ⟨rooted, other, otherOk, inside, honestIndex⟩ => ?_⟩
      rw [committeeOk, Except.ok.injEq] at otherOk
      subst otherOk
      exact flagged rooted index inside honestIndex)
    state 0
    ⟨state.balances, state.previousEpochParticipation, state.currentEpochParticipation, rfl⟩
    (by rwa [Nat.zero_mul, Nat.add_zero]) participation (by rwa [Nat.zero_add])
  -- A flag once set stays set, so each honest member of each committee ends with the target flag.
  exact ⟨after, folded, fun vote member rooted committee committeeOk index inside honestIndex =>
    flagged vote member index ⟨rooted, committee, committeeOk, inside, honestIndex⟩⟩

/-- From Electra until Gloas, the attestation steps accept the honest aggregates of slots.

Each aggregate covers the committees of the slot of its data that have an honest member.

The data and the state meet the checks of the attestation step, and the state is within a budget.

The budget must leave room for the rewards of the proposer, one for each aggregate of the list.

The secret keys of the honest members of the committees of each slot must not sum to zero.

The active validators times the committees of each epoch must fit in 64 bits.

Each honest member of each committee of each slot then holds the timely target flag.

That needs the state to hold the target root for the first slot of the target epoch. -/
theorem foldlM_processAttestation_honestSlotAggregate {budget scoreBound : Nat}
    (electra : .pectra ≤ fork) (beforeGloas : fork < .glamsterdam)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (parentSlot : Slot) (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    {datas : List AttestationData}
    -- Each reward is at most 64 base reward ceilings for each validator of the registry, over 448.
    --
    -- The budget must also leave room for that bound before the division.
    (room : budget + datas.length * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (recent : ∀ data ∈ datas, data.target.epoch = getPreviousEpoch state ∨
      data.target.epoch = getCurrentEpoch state)
    (slotEpoch : ∀ data ∈ datas, data.target.epoch = computeEpochAtSlot preset data.slot)
    (past : ∀ data ∈ datas, data.slot.toNat < state.slot.toNat)
    (early : ∀ data ∈ datas,
      data.slot.toNat + preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤ state.slot.toNat)
    (indexed : ∀ data ∈ datas, data.index = 0)
    (shuffleRoom : ∀ data ∈ datas, (getActiveValidatorIndices state data.target.epoch).length *
      ((getCommitteeCountPerSlot state data.target.epoch).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    (source : ∀ data ∈ datas, data.source =
      if data.target.epoch = getCurrentEpoch state then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint)
    (registered : ∀ index ∈ honest, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : ∀ data ∈ datas, ∀ committees, (List.range
        (getCommitteeCountPerSlot state data.target.epoch).toNat).mapM
      (fun position => getBeaconCommittee state data.slot position.toUInt64) = .ok committees →
        (((committees.flatMap (honestSigners honest)).map key).map (·.val)).sum ≠ 0)
    (proposer : ∃ index, getBeaconProposerIndex state = .ok index ∧
      index.toNat < state.validators.data.size)
    {attestations : List (Attestation preset fork)}
    (built : List.Forall₂ (fun data attestation =>
      honestSlotAggregate electra config state honest key data = .ok attestation)
        datas attestations) :
    ∃ after, attestations.foldlM (processAttestation config .bls · parentSlot ·) state = .ok after ∧
      ∀ data ∈ datas, getBlockRoot state data.target.epoch = .ok data.target.root →
        ∀ committeeIndex committee,
          committeeIndex < getCommitteeCountPerSlot state data.target.epoch →
          getBeaconCommittee state data.slot committeeIndex = .ok committee →
            ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation after
              (Nat.le_trans (by decide) electra) (data.target.epoch == getCurrentEpoch state))
                index.toNat := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  -- The registry has a validator, so the ceiling of a base reward fits.
  have positive : 0 < state.validators.data.size := by
    obtain ⟨index, -, inside⟩ := proposer
    omega
  -- Each aggregate passes on every state like the first, which has spent no budget.
  obtain ⟨after, folded, flagged⟩ := foldlM_processAttestation_of_accepted_from altair beforeGloas
    increment scaled positive
    (fun (data : AttestationData) index =>
      getBlockRoot state data.target.epoch = .ok data.target.root ∧
      ∃ committeeIndex committee,
        committeeIndex < getCommitteeCountPerSlot state data.target.epoch ∧
        getBeaconCommittee state data.slot committeeIndex = .ok committee ∧
        index ∈ committee ∧ index ∈ honest)
    (fun data => data.target.epoch == getCurrentEpoch state)
    (((List.forall₂_and_left _ _).mpr
      ⟨fun data member => And.intro (recent data member) (And.intro (slotEpoch data member)
        (And.intro (past data member) (And.intro (early data member)
          (And.intro (indexed data member) (And.intro (shuffleRoom data member)
            (And.intro (source data member) (sum data member))))))), built⟩).imp
      fun data attestation ⟨⟨recent, slotEpoch, past, early, indexed, shuffleRoom, source, sum⟩,
        head⟩ funds first shaped holds participation room => by
      -- The committees of the slot have values, since the aggregate reads them.
      obtain ⟨committees, committeesOk⟩ := committees_of_honestSlotAggregate electra head
      rw [← slotEpoch] at committeesOk
      obtain ⟨balances, previous, current, rfl⟩ := shaped
      -- The step reads only what the first state holds, so the honest aggregate is accepted.
      obtain ⟨middle, processed, flagged⟩ := processAttestation_honestSlotAggregate
        (state := { state with
          balances := balances, previousEpochParticipation := previous,
          currentEpochParticipation := current }) electra beforeGloas parentSlot roots slotRoom
        increment scaled holds participation room recent slotEpoch past early indexed
        (by rw [← slotEpoch]; exact committeesOk) (by rw [← slotEpoch]; exact shuffleRoom) source
        registered (sum committees committeesOk) proposer head
      refine ⟨middle, processed, fun index ⟨rooted, committeeIndex, committee, below, committeeOk,
        inside, honestIndex⟩ => ?_⟩
      exact flagged rooted committee (mem_of_mapM_getBeaconCommittee committeesOk
        (UInt64.lt_iff_toNat_lt.mp below) committeeOk) index inside honestIndex)
    state 0
    ⟨state.balances, state.previousEpochParticipation, state.currentEpochParticipation, rfl⟩
    (by rwa [Nat.zero_mul, Nat.add_zero]) participation (by rwa [Nat.zero_add])
  exact ⟨after, folded, fun data member rooted committeeIndex committee below committeeOk index
    inside honestIndex => flagged data member index
      ⟨rooted, committeeIndex, committee, below, committeeOk, inside, honestIndex⟩⟩

/-- From Altair until Gloas, the attestation steps keep a budget that grows with each step.

Each step may raise it by one reward share, the bound of the reward of the proposer.

The registry must not be empty, and the budget must leave room for every share and the ceiling.

The flags keep one entry for each validator. -/
theorem foldlM_processAttestation_withinBudget {budget scoreBound : Nat}
    {checks : SignatureChecks} {parentSlot : Slot} (altair : .altair ≤ fork)
    (beforeGloas : fork < .glamsterdam) (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (positive : 0 < state.validators.data.size) :
    ∀ {attestations : List (Attestation preset fork)} {after : BeaconState preset fork}
      {spent : Nat} {first : BeaconState preset fork},
      first.validators = state.validators →
      WithinBudget (budget + spent * (state.validators.data.size *
        (64 * preset.baseRewardCeiling) / 448)) scoreBound first →
      ParticipationMatches first →
      budget + (spent + attestations.length) * (state.validators.data.size *
        (64 * preset.baseRewardCeiling) / 448) +
          state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64 →
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok after →
      after.validators = state.validators ∧
        WithinBudget (budget + (spent + attestations.length) * (state.validators.data.size *
          (64 * preset.baseRewardCeiling) / 448)) scoreBound after ∧ ParticipationMatches after
  | [], after, spent, first, validators, holds, participation, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simpa using ⟨validators, holds, participation⟩
  | attestation :: rest, after, spent, first, validators, holds, participation, room,
      computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, processed, computed⟩ := computed
    rw [List.length_cons] at room
    -- The step spends one share of the budget, and the rest of the list runs on its state.
    obtain ⟨middleValidators, raisedHolds, raisedParticipation, -⟩ :=
      processAttestation_budgetStep altair beforeGloas increment scaled positive validators holds
        participation room processed
    have kept := foldlM_processAttestation_withinBudget altair beforeGloas increment scaled
      positive (spent := spent + 1) middleValidators raisedHolds raisedParticipation
      (by rw [show spent + 1 + rest.length = spent + (rest.length + 1) by omega]; exact room)
      computed
    rw [show spent + 1 + rest.length = spent + (rest.length + 1) by omega] at kept
    exact kept

end EthLib.Consensus
