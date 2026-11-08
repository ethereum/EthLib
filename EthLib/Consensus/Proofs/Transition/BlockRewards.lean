module

public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.SyncAggregate

/-!
# Proofs: the rewards paid inside a block

From Altair, a block pays its proposer for slashings, attestations and the sync aggregate.

This module covers the attestations and the sync aggregate.

An attestation pays the proposer of the slot one reward.

That reward sums the weighted base reward of each flag newly set, over the attesters.

The sum is divided by `(64 - 8) * 64 / 8 = 448`, rounding down.

Each sync committee member that signed earns the participant reward, and the proposer a share.

Each member that did not sign pays the participant reward, stopping at zero.

The participant reward is the total base reward of a slot, weighted and split among the members.

The proposer share is the participant reward times 8, over 64 - 8 = 56, rounding down.

These rules hold at every fork from Altair.

From Electra the attesters may come from several committees, as [EIP-7549] specifies.

From Gloas an attestation also weighs a builder payment, as [EIP-7732] specifies.

Neither changes how the rewards are computed.

No EIP specifies the Altair rewards themselves, so this comment states them.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## The sync aggregate -/

/-- The steps of the sync rewards, in committee order, read at one balance.

A member that signed adds the reward to its balance, and the proposer adds its share to its own.

A member that did not sign subtracts the reward from its balance, stopping at zero.

No addition overflows.

The proposer is read only when a member signed. -/
theorem foldlM_applySyncReward_balance {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} {chosen : ValidatorIndex}
    (read : ∀ index, proposer = .ok index → index = chosen) :
    ∀ {members : List (ValidatorIndex × Bool)} {state after : BeaconState preset fork},
      members.foldlM (applySyncReward reward proposerReward proposer) state = .ok after →
      ((∃ member ∈ members, member.2 = true) → proposer = .ok chosen) ∧
      ∀ j balance, state.balances.data[j]? = some balance → ∃ final,
        after.balances.data[j]? = some final ∧ final.toNat = members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then reward.toNat else 0) +
            (if chosen.toNat = j then proposerReward.toNat else 0)
          else if member.1.toNat = j then balance - reward.toNat else balance) balance.toNat
  | [], state, after, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun ⟨_, absent, _⟩ => absurd absent List.not_mem_nil,
      fun _ balance found => ⟨balance, found, rfl⟩⟩
  | member :: members, state, after, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    obtain ⟨later, balances⟩ := foldlM_applySyncReward_balance read folded
    obtain ⟨index, signed⟩ := member
    unfold applySyncReward at stepped
    cases signed with
    | true =>
      simp only [↓reduceIte, bind_ok_iff, liftAccessor_ok] at stepped
      obtain ⟨raised, raisedOk, paid, paidOk, paidBalance⟩ := stepped
      obtain rfl := read paid paidOk
      refine ⟨fun _ => paidOk, fun j balance found => ?_⟩
      obtain ⟨first, firstFound, firstValue⟩ := balance_increaseBalance raisedOk found
      obtain ⟨second, secondFound, secondValue⟩ := balance_increaseBalance paidBalance firstFound
      obtain ⟨final, finalFound, finalValue⟩ := balances j second secondFound
      refine ⟨final, finalFound, ?_⟩
      rw [finalValue, secondValue, firstValue]
      rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, liftAccessor_ok] at stepped
      refine ⟨fun ⟨other, member, signer⟩ => ?_, fun j balance found => ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · cases signer
        · exact later ⟨other, member, signer⟩
      · obtain ⟨first, firstFound, firstValue⟩ := balance_decreaseBalance stepped found
        obtain ⟨final, finalFound, finalValue⟩ := balances j first firstFound
        refine ⟨final, finalFound, ?_⟩
        rw [finalValue, firstValue]
        rfl

/-- The reward of a sync committee member that signs, for one slot.

It is the base reward per increment times the active increments, weighted by the sync weight.

That product is divided by the weight denominator, the slots of an epoch and the committee size.

Each division rounds down, and the base reward per increment rounds down too. -/
theorem syncParticipantReward_ok {reward : Gwei}
    (computed : syncParticipantReward state = .ok reward) :
    ∃ total perIncrement, getTotalActiveBalance state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement ∧
      perIncrement.toNat = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        preset.BASE_REWARD_FACTOR.toNat / total.toNat.sqrt ∧
      reward.toNat = perIncrement.toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * SYNC_REWARD_WEIGHT.toNat /
          WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
            preset.SYNC_COMMITTEE_SIZE.toNat := by
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨total, totalOk, perIncrement, perIncrementOk, computed⟩ := computed
  obtain ⟨increments, incrementsOk, base, baseOk, weighted, weightedOk, perEpoch, perEpochOk,
    perSlot, perSlotOk, rewardOk⟩ := computed
  have perIncrementValue := perIncrementOk
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff,
    bind_ok_iff] at perIncrementValue
  obtain ⟨scaled, scaledOk, rootOk⟩ := perIncrementValue
  rw [mulChecked_ok_iff] at scaledOk baseOk weightedOk
  rw [divChecked_ok_iff] at incrementsOk perEpochOk perSlotOk rewardOk rootOk
  refine ⟨total, perIncrement, totalOk, perIncrementOk, ?_, ?_⟩
  · rw [rootOk.2, scaledOk.2, toNat_integerSquareroot]
  · rw [rewardOk.2, perSlotOk.2, perEpochOk.2, weightedOk.2, baseOk.2, incrementsOk.2]

/-- The sync aggregate step, from Altair, at each balance.

The members are the first validators that hold the keys of the committee, in committee order.

Each member that signed earns the participant reward, and the proposer earns its share.

That share is the reward times the proposer weight, over the denominator less that weight.

It rounds down.

Each member that did not sign pays the participant reward, stopping at zero.

The steps run in committee order, so a member listed twice is paid twice.

No addition overflows.

The proposer is the one of the state before the step, read only when a member signed. -/
theorem processSyncAggregate_balance {config : Config} {checks : SignatureChecks}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ∃ (reward proposerReward : Gwei) (members : Array ValidatorIndex) (chosen : ValidatorIndex),
      syncParticipantReward state = .ok reward ∧
      proposerReward.toNat =
        reward.toNat * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) ∧
      (state.currentSyncCommittee altair).value.pubkeys.toArray.mapM
        (validatorIndexOfPubkey state) = .ok members ∧
      ((∃ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
        member.2 = true) → getBeaconProposerIndex state = .ok chosen) ∧
      ∀ j balance, state.balances.data[j]? = some balance → ∃ final,
        after.balances.data[j]? = some final ∧
        final.toNat = (members.zip aggregate.syncCommitteeBits.bits.toArray).toList.foldl
          (fun balance member =>
            if member.2 then balance + (if member.1.toNat = j then reward.toNat else 0) +
              (if chosen.toNat = j then proposerReward.toNat else 0)
            else if member.1.toNat = j then balance - reward.toNat else balance) balance.toNat := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposerReward, proposerRewardOk,
    members, membersOk, folded⟩ := computed
  obtain ⟨scaled, scaledOk, proposerRewardOk⟩ := proposerRewardOk
  rw [mulChecked_ok_iff] at scaledOk
  rw [divChecked_ok_iff] at proposerRewardOk
  -- The proposer is fixed when the state has one, and otherwise no member signed.
  let chosen : ValidatorIndex := match getBeaconProposerIndex state with
    | .ok index => index
    | .error _ => 0
  have read : ∀ index, getBeaconProposerIndex state = .ok index → index = chosen := by
    intro index found
    simp [chosen, found]
  rw [← Array.foldlM_toList] at folded
  obtain ⟨signed, balances⟩ := foldlM_applySyncReward_balance read folded
  refine ⟨reward, proposerReward, members, chosen, rewardOk, ?_, membersOk, signed, balances⟩
  rw [proposerRewardOk.2, scaledOk.2]
  rfl

/-! ## The proposer reward of an attestation -/

/-- Adding one participation flag keeps whether another flag is set. -/
theorem hasFlag_addFlag_of_ne (flags : ParticipationFlags)
    {added other : Fin PARTICIPATION_FLAG_WEIGHTS.length} (different : other ≠ added) :
    hasFlag (addFlag flags added.val.toUInt64) other.val.toUInt64 =
      hasFlag flags other.val.toUInt64 := by
  -- The bits of two different flags do not overlap.
  have apart : ∀ added other : Fin PARTICIPATION_FLAG_WEIGHTS.length, other ≠ added →
      flagBit added.val.toUInt64 &&& flagBit other.val.toUInt64 = 0 := by decide
  have disjoint := congrArg UInt8.toBitVec (apart added other different)
  simp only [hasFlag, addFlag]
  congr 1
  apply UInt8.toBitVec_inj.mp
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or]
  ext k
  have bit := congrArg (·[k]) disjoint
  simp only [UInt8.toBitVec_and, BitVec.getElem_and, UInt8.toBitVec_zero,
    BitVec.getElem_zero] at bit
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases h₁ : (flags.toBitVec)[k] <;> cases h₂ : (flagBit added.val.toUInt64).toBitVec[k] <;>
    cases h₃ : (flagBit other.val.toUInt64).toBitVec[k] <;> simp_all

/-- The proposer numerator of one attester: its weighted base reward for each flag newly set.

A flag is newly set when the attestation earns it and the attester's flags did not have it. -/
def newFlagsNumerator (earned : List UInt64) (flags : ParticipationFlags) (base : Gwei) : Nat :=
  ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
    if flag.val.toUInt64 ∈ earned ∧ hasFlag flags flag.val.toUInt64 = false then
      base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum

/-- Setting the flags of one attester in turn, with no flag twice in the list.

A flag outside the list keeps whether it is set.

The numerator gains the weighted base reward of each flag newly set, without overflow.

Whether a flag is newly set is read from the flags before the first step. -/
private theorem foldlM_addFlagReward {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} :
    ∀ {flagList : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)} {flags flags' : ParticipationFlags}
      {numerator numerator' : Gwei}, flagList.Nodup →
      flagList.foldlM (addFlagReward state total earned index) (flags, numerator) =
        .ok (flags', numerator') →
      (∀ flag, flag ∉ flagList →
        hasFlag flags' flag.val.toUInt64 = hasFlag flags flag.val.toUInt64) ∧
      ∃ base, (∀ flag ∈ flagList, flag.val.toUInt64 ∈ earned →
          hasFlag flags flag.val.toUInt64 = false → getBaseReward state total index = .ok base) ∧
        numerator'.toNat = numerator.toNat + (flagList.map fun flag =>
          if flag.val.toUInt64 ∈ earned ∧ hasFlag flags flag.val.toUInt64 = false then
            base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum
  | [], flags, flags', numerator, numerator', _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    exact ⟨fun _ _ => rfl, 0, fun _ absent => absurd absent List.not_mem_nil, by simp⟩
  | flag :: flagList, flags, flags', numerator, numerator', distinct, computed => by
    rw [List.nodup_cons] at distinct
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middleFlags, middle⟩, stepped, folded⟩ := computed
    obtain ⟨kept, base, based, sum⟩ := foldlM_addFlagReward distinct.2 folded
    -- The step sets at most its own flag, so the later flags read as before it.
    have same : ∀ other ∈ flagList,
        hasFlag middleFlags other.val.toUInt64 = hasFlag flags other.val.toUInt64 := by
      intro other member
      have different : other ≠ flag := fun equal => distinct.1 (equal ▸ member)
      simp only [addFlagReward] at stepped
      split at stepped
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at stepped
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := stepped
        exact hasFlag_addFlag_of_ne flags different
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
        obtain ⟨rfl, _⟩ := stepped
        rfl
    have rest : (flagList.map fun other =>
        if other.val.toUInt64 ∈ earned ∧ hasFlag middleFlags other.val.toUInt64 = false then
          base.toNat * PARTICIPATION_FLAG_WEIGHTS[other].toNat else 0) =
        flagList.map fun other =>
          if other.val.toUInt64 ∈ earned ∧ hasFlag flags other.val.toUInt64 = false then
            base.toNat * PARTICIPATION_FLAG_WEIGHTS[other].toNat else 0 :=
      List.map_congr_left fun other member => by rw [same other member]
    have keptOutside : ∀ other, other ∉ flag :: flagList →
        hasFlag flags' other.val.toUInt64 = hasFlag flags other.val.toUInt64 := by
      intro other absent
      rw [kept other (fun member => absent (List.mem_cons_of_mem _ member))]
      have different : other ≠ flag := fun equal => absent (equal ▸ List.mem_cons_self)
      simp only [addFlagReward] at stepped
      split at stepped
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at stepped
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := stepped
        exact hasFlag_addFlag_of_ne flags different
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
        obtain ⟨rfl, _⟩ := stepped
        rfl
    simp only [addFlagReward] at stepped
    split at stepped
    · rename_i newly
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨reward, rewardOk, weighted, weightedOk, added, addedOk, _, rfl⟩ := stepped
      rw [mulChecked_ok_iff] at weightedOk
      rw [addChecked_ok_iff] at addedOk
      -- The base reward is read once, so every newly set flag reads the same one.
      have agree : ∀ other ∈ flagList, other.val.toUInt64 ∈ earned →
          hasFlag flags other.val.toUInt64 = false → base = reward := by
        intro other member earnedOther unset
        have := based other member earnedOther (by rw [same other member]; exact unset)
        rw [rewardOk] at this
        exact (Except.ok.inj this).symm
      refine ⟨keptOutside, reward, fun other member earnedOther unset => ?_, ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact rewardOk
        · rw [← agree other member earnedOther unset]
          exact based other member earnedOther (by rw [same other member]; exact unset)
      · rw [sum, rest, addedOk.2, weightedOk.2, List.map_cons, List.sum_cons]
        simp only [newly, and_self, ↓reduceIte]
        have congr : (flagList.map fun other =>
            if other.val.toUInt64 ∈ earned ∧ hasFlag flags other.val.toUInt64 = false then
              base.toNat * PARTICIPATION_FLAG_WEIGHTS[other].toNat else 0) =
            flagList.map fun other =>
              if other.val.toUInt64 ∈ earned ∧ hasFlag flags other.val.toUInt64 = false then
                reward.toNat * PARTICIPATION_FLAG_WEIGHTS[other].toNat else 0 :=
          List.map_congr_left fun other member => by
            split
            · rename_i both
              rw [agree other member both.1 both.2]
            · rfl
        rw [congr]
        omega
    · rename_i old
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨rfl, rfl⟩ := stepped
      refine ⟨keptOutside, base, fun other member earnedOther unset => ?_, ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact absurd ⟨earnedOther, unset⟩ old
        · exact based other member earnedOther (by rw [same other member]; exact unset)
      · rw [sum, rest, List.map_cons, List.sum_cons]
        simp only [old, ↓reduceIte]
        omega

/-- The flags of some attesters, each named once, set in turn.

The flags of the other validators stay.

The numerator gains, for each attester, the weighted base reward of each flag newly set.

Whether a flag is newly set is read from the attester's flags before the attestation. -/
theorem foldlM_addAttesterFlags {total : Gwei} {earned : List UInt64} :
    ∀ {attesters : List ValidatorIndex} {participation : EpochParticipation preset fork}
      {numerator : Gwei} {result : EpochParticipation preset fork × Gwei},
      (attesters.map UInt64.toNat).Nodup →
      attesters.foldlM (addAttesterFlags state total earned) (participation, numerator) =
        .ok result →
      (∀ i, (∀ attester ∈ attesters, attester.toNat ≠ i) →
        result.1.data[i]? = participation.data[i]?) ∧
      ∃ shares : List (ValidatorIndex × ParticipationFlags × Gwei),
        shares.map (·.1) = attesters ∧
        (∀ share ∈ shares, participation.data[share.1.toNat]? = some share.2.1 ∧
          ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, flag.val.toUInt64 ∈ earned →
            hasFlag share.2.1 flag.val.toUInt64 = false →
              getBaseReward state total share.1 = .ok share.2.2) ∧
        result.2.toNat = numerator.toNat +
          (shares.map fun share => newFlagsNumerator earned share.2.1 share.2.2).sum
  | [], participation, numerator, result, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ _ => rfl, [], rfl, fun _ absent => absurd absent List.not_mem_nil, by simp⟩
  | attester :: attesters, participation, numerator, result, distinct, computed => by
    rw [List.map_cons, List.nodup_cons] at distinct
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleNumerator⟩, stepped, folded⟩ := computed
    obtain ⟨kept, shares, named, facts, sum⟩ := foldlM_addAttesterFlags distinct.2 folded
    unfold addAttesterFlags at stepped
    dsimp only at stepped
    split at stepped
    · rename_i inside
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨⟨flags, raised⟩, loop, written, rfl⟩ := stepped
      obtain ⟨-, base, based, raisedValue⟩ := foldlM_addFlagReward (List.nodup_finRange _) loop
      -- The step writes only the attester's own flags.
      have other : ∀ i, attester.toNat ≠ i → middle.data[i]? = participation.data[i]? := by
        intro i different
        rw [← written]
        simp [different]
      refine ⟨fun i absent => ?_, (attester, participation.data[attester.toNat], base) :: shares,
        by simp [named], fun share member => ?_, ?_⟩
      · rw [kept i fun later member => absent later (List.mem_cons_of_mem _ member)]
        exact other i (absent attester List.mem_cons_self)
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨Array.getElem?_eq_getElem inside, fun flag earnedFlag unset =>
            based flag (List.mem_finRange _) earnedFlag unset⟩
        · obtain ⟨found, reads⟩ := facts share member
          refine ⟨?_, reads⟩
          rw [← other share.1.toNat fun same => distinct.1 ?_]
          · exact found
          · rw [same, ← named]
            exact List.mem_map_of_mem (List.mem_map_of_mem member)
      · rw [sum, raisedValue, List.map_cons, List.sum_cons]
        simp only [newFlagsNumerator]
        omega
    · cases stepped

/-- The attesters of an attestation name each validator once. -/
theorem getAttestingIndices_nodup {attestation : Attestation preset fork}
    {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    (attesters.map UInt64.toNat).Nodup :=
  List.pairwise_map.mpr ((getAttestingIndices_sorted computed).imp fun less same =>
    UInt64.ne_of_lt less (UInt64.toNat_inj.mp same))

/-- Writing the flags of an epoch keeps the proposer of the slot, which reads no flag. -/
theorem getBeaconProposerIndex_setEpochParticipation (current : Bool)
    (participation : EpochParticipation preset fork) :
    getBeaconProposerIndex (setEpochParticipation state current participation) =
      getBeaconProposerIndex state := by
  cases current <;> rfl

/-- The balances after an attestation, from Altair, at every fork.

The proposer of the slot earns one reward, and every other balance stays.

That reward is the numerator over `(64 - 8) * 64 / 8 = 448`, rounding down.

The numerator sums, over the attesters, the weighted base reward of each flag newly set.

A flag is newly set when the attestation earns it and the attester's flags did not have it.

Those flags are the attester's flags in the epoch of the target, before the attestation.

No addition overflows.

From Electra the attesters may come from several committees.

From Gloas the attestation also weighs a builder payment, which changes no balance. -/
theorem processAttestationAltair_balance {config : Config} {checks : SignatureChecks}
    {attestation : Attestation preset fork} {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed : processAttestationAltair config checks state attestation altair parentSlot =
      .ok after) :
    ∃ earned total attesters proposer, getAttestationParticipationFlagIndices state
        attestation.data (state.slot - attestation.data.slot) parentSlot = .ok earned ∧
      getTotalActiveBalance state = .ok total ∧
      getAttestingIndices state attestation = .ok attesters ∧
      getBeaconProposerIndex state = .ok proposer ∧
      ∃ shares : List (ValidatorIndex × ParticipationFlags × Gwei),
        shares.map (·.1) = attesters ∧
        (∀ share ∈ shares, (if attestation.data.target.epoch == getCurrentEpoch state then
            state.currentEpochParticipation altair
          else state.previousEpochParticipation altair).data[share.1.toNat]? = some share.2.1 ∧
          ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, flag.val.toUInt64 ∈ earned →
            hasFlag share.2.1 flag.val.toUInt64 = false →
              getBaseReward state total share.1 = .ok share.2.2) ∧
        ∀ j balance, state.balances.data[j]? = some balance → ∃ final,
          after.balances.data[j]? = some final ∧
          final.toNat = balance.toNat + if proposer.toNat = j then
            (shares.map fun share => newFlagsNumerator earned share.2.1 share.2.2).sum /
              ((WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
                PROPOSER_WEIGHT.toNat)
          else 0 := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _, total, totalOk,
    attesters, attestersOk, ⟨updated, numerator⟩, folded, proposer, proposerOk, raised, raisedOk,
    computed⟩ := computed
  rw [getBeaconProposerIndex_setEpochParticipation] at proposerOk
  obtain ⟨-, shares, named, facts, sum⟩ :=
    foldlM_addAttesterFlags (getAttestingIndices_nodup attestersOk) folded
  refine ⟨earned, total, attesters, proposer, earnedOk, totalOk, attestersOk, proposerOk, shares,
    named, facts, fun j balance found => ?_⟩
  -- Writing the flags keeps the balances, and from Gloas so does weighing the payment.
  have balances : after.balances = raised.balances := by
    split at computed
    · rw [recordPaymentWeight_eq computed]
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      rw [computed]
  have written : (setEpochParticipation state
      (attestation.data.target.epoch == getCurrentEpoch state) updated).balances.data[j]? =
      some balance := by
    unfold setEpochParticipation
    split <;> exact found
  obtain ⟨final, finalFound, finalValue⟩ := balance_increaseBalance raisedOk written
  refine ⟨final, balances ▸ finalFound, ?_⟩
  rw [finalValue, UInt64.toNat_div, sum]
  have denominator : ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT).toNat = (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) *
        WEIGHT_DENOMINATOR.toNat / PROPOSER_WEIGHT.toNat := by decide
  rw [denominator]
  simp

/-- From Altair, the attestation step is the one of Altair and later forks. -/
theorem processAttestation_of_altair {config : Config} {checks : SignatureChecks}
    {attestation : Attestation preset fork} {parentSlot : Slot} (altair : .altair ≤ fork) :
    processAttestation config checks state parentSlot attestation =
      processAttestationAltair config checks state attestation altair parentSlot := by
  simp [processAttestation, altair]

end EthLib.Consensus
