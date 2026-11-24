module

public import EthLib.Consensus.Proofs.HonestAttestationList
public import EthLib.Consensus.Proofs.HonestBlockInput
import EthLib.Consensus.Proofs.Containers.Block
import EthLib.Consensus.Proofs.HonestBlockDeposits
import EthLib.Consensus.Proofs.Transition.BlockLedger
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.SyncAggregate

/-!
# Proofs: the block of an honest proposer passes its step in a run

From Altair until Gloas, the block passes, with its signature and its state root checked.

It carries honest attestations of some committees, or from Electra honest aggregates of slots.

On mainnet a block holds at most 128 attestations before Electra, and 8 from Electra.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config}

/-- The honest attestation of a committee of a recent slot is the same on two states.

The two states must agree on what the attestations read. -/
theorem honestAttestation_eq_of_kept {state input : BeaconState preset fork}
    (kept : AttestationReadsKept state input) {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {data : AttestationData}
    {committeeIndex : CommitteeIndex}
    (low : getPreviousEpoch state ≤ computeEpochAtSlot preset data.slot)
    (high : computeEpochAtSlot preset data.slot ≤ getCurrentEpoch state) :
    honestAttestation config input honest key data committeeIndex =
      honestAttestation config state honest key data committeeIndex := by
  -- The committees of the slot of the data are the same on both states.
  have committees : ∀ index, getBeaconCommittee input data.slot index =
      getBeaconCommittee state data.slot index :=
    fun index => kept.committees _ low high data.slot index rfl
  -- The signature reads only the fork versions and the genesis validators root.
  have signature : getAttestationSignature config input = getAttestationSignature config state := by
    funext data key
    unfold getAttestationSignature signAtEpoch getDomain getCurrentEpoch
    rw [kept.forkVersions, kept.genesisValidatorsRoot, kept.slot]
  unfold honestAttestation constructSingleAttestation constructAttestation constructAggregate
    constructAggregateOfSingleAttestations
  simp only [committees, signature]

/-- From Electra, the honest aggregate of a recent slot is the same on two states.

The two states must agree on what the attestations read. -/
theorem honestSlotAggregate_eq_of_kept (electra : .pectra ≤ fork)
    {state input : BeaconState preset fork} (kept : AttestationReadsKept state input)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {data : AttestationData}
    (low : getPreviousEpoch state ≤ computeEpochAtSlot preset data.slot)
    (high : computeEpochAtSlot preset data.slot ≤ getCurrentEpoch state) :
    honestSlotAggregate electra config input honest key data =
      honestSlotAggregate electra config state honest key data := by
  -- The count of committees reads only the registry.
  have count : ∀ epoch, getCommitteeCountPerSlot input epoch =
      getCommitteeCountPerSlot state epoch := by
    intro epoch
    unfold getCommitteeCountPerSlot getActiveValidatorIndices
    rw [kept.validators]
  have committees : ∀ index, getBeaconCommittee input data.slot index =
      getBeaconCommittee state data.slot index :=
    fun index => kept.committees _ low high data.slot index rfl
  -- The honest attestation of each committee is the same on both states.
  have attestations : honestAttestation config input honest key data =
      honestAttestation config state honest key data :=
    funext fun _ => honestAttestation_eq_of_kept kept low high
  unfold honestSlotAggregate honestCommittees
  simp only [count, committees, attestations]

/-! ## The sync aggregate of an honest block -/

/-- The sync reward of one member has a value, when the budget leaves room for it.

The whole increments of the total active balance are at most twice those of the largest cap.

That bound is for each validator of the registry.

So the weighted base reward is at most four ceilings per validator, which fits. -/
private theorem syncParticipantReward_exists {budget scoreBound : Nat}
    {state : BeaconState preset fork} (holds : WithinBudget budget scoreBound state)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (slots : preset.SLOTS_PER_EPOCH ≠ 0) (members : preset.SYNC_COMMITTEE_SIZE ≠ 0)
    (positive : 0 < state.validators.data.size)
    (fits : budget + state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64) :
    ∃ reward, syncParticipantReward state = .ok reward := by
  obtain ⟨total, totalOk, low, bounded⟩ := getTotalActiveBalance_exists_ok holds.within
    (by have := holds.effectiveBalanceSum_le; omega)
  obtain ⟨per, perOk, perLe⟩ := getBaseRewardPerIncrement_le increment scaled low
  have positiveE : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => increment (UInt64.toNat_inj.mp (by simpa using zero))
  have ratio : 1 ≤ preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    (Nat.one_le_div_iff positiveE).mpr incrementLe
  -- Each effective balance is at most the largest cap, so their sum is at most that many caps.
  have summed : effectiveBalanceSum state ≤
      state.validators.data.size * preset.largestEffectiveBalance := by
    unfold effectiveBalanceSum
    have := List.sum_le_length_nsmul (state.validators.data.toList.map (·.effectiveBalance.toNat))
      preset.largestEffectiveBalance fun balance member => by
        obtain ⟨validator, inside, rfl⟩ := List.mem_map.mp member
        exact (UInt64.le_iff_toNat_le.mp (holds.capped validator (by simpa using inside))).trans
          (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork validator)
    simpa using this
  -- The whole increments of the total are at most two for each validator and cap ratio.
  have incrementsLe : total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * (state.validators.data.size *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
    have one : 1 ≤ state.validators.data.size *
        (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rcases bounded with rfl | le
    · rw [Nat.div_self positiveE]
      omega
    · -- The cap is less than one increment more than its whole increments.
      have capLt := Nat.lt_mul_div_succ preset.largestEffectiveBalance positiveE
      have below : state.validators.data.size * preset.largestEffectiveBalance /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat < state.validators.data.size *
            (preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) :=
        (Nat.div_lt_iff_lt_mul positiveE).mpr (by
          rw [Nat.mul_assoc, Nat.mul_comm _ preset.EFFECTIVE_BALANCE_INCREMENT.toNat]
          exact Nat.mul_lt_mul_of_pos_left capLt (by omega))
      have atMost := Nat.div_le_div_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
        (le.trans summed)
      rw [Nat.mul_add, Nat.mul_one] at below
      have := Nat.le_mul_of_pos_right state.validators.data.size ratio
      omega
  -- So the base reward of the whole balance is at most two ceilings per validator.
  have baseLe : per.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      2 * (state.validators.data.size * preset.baseRewardCeiling) := by
    refine (Nat.mul_le_mul perLe incrementsLe).trans (le_of_eq ?_)
    unfold Preset.baseRewardCeiling
    ring
  have spread : state.validators.data.size * (64 * preset.baseRewardCeiling) =
      64 * (state.validators.data.size * preset.baseRewardCeiling) := by ring
  have baseFits : per.toNat * (total / preset.EFFECTIVE_BALANCE_INCREMENT).toNat < 2 ^ 64 := by
    rw [UInt64.toNat_div]
    omega
  have weightedFits : (per * (total / preset.EFFECTIVE_BALANCE_INCREMENT)).toNat *
      SYNC_REWARD_WEIGHT.toNat < 2 ^ 64 := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt baseFits, UInt64.toNat_div,
      show SYNC_REWARD_WEIGHT.toNat = 2 from rfl]
    omega
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff]
  exact ⟨_, total, totalOk, per, perOk, _,
    Uint64.divChecked_ok_iff.mpr ⟨increment, UInt64.toNat_div _ _⟩, _,
    Uint64.mulChecked_of_lt baseFits, _, Uint64.mulChecked_of_lt weightedFits, _,
    Uint64.divChecked_ok_iff.mpr ⟨by decide, UInt64.toNat_div _ _⟩, _,
    Uint64.divChecked_ok_iff.mpr ⟨slots, UInt64.toNat_div _ _⟩,
    Uint64.divChecked_ok_iff.mpr ⟨members, UInt64.toNat_div _ _⟩⟩

/-- With no bit set, the sync aggregate checks the empty list of keys.

The committee must not be empty, or no bit set would mean that every member signed. -/
private theorem syncParticipantPubkeys_none [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (committee : SyncCommittee preset)
    {bits : Serialization.Ssz.Bitvector preset.SYNC_COMMITTEE_SIZE.toNat}
    (none : ∀ bit ∈ bits.bits.toList, bit = false) :
    syncParticipantPubkeys committee bits = .ok #[] := by
  have counted : bits.bits.toArray.countP id = 0 :=
    Array.countP_eq_zero.mpr fun bit member => by
      simp [none bit (by simpa using member)]
  have size := NeZero.ne preset.SYNC_COMMITTEE_SIZE.toNat
  unfold syncParticipantPubkeys
  -- No pair of a key and a bit has its bit set, so the list of signing keys is empty.
  have empty : (committee.pubkeys.toArray.zip bits.bits.toArray).filter (·.2) = #[] := by
    refine Array.filter_eq_empty_iff.mpr fun pair member => ?_
    have := none pair.2 (by simpa using (Array.of_mem_zip member).2)
    simp [this]
  simp only [counted, empty, Ne.symm size, Nat.not_lt_zero, ↓reduceIte, Array.map_empty]
  rfl

/-- Each member that did not sign loses the participant reward.

That passes for members of the registry. -/
private theorem foldlM_applySyncReward_unsigned {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} :
    ∀ (members : List (ValidatorIndex × Bool)) (state : BeaconState preset fork),
      (∀ member ∈ members, member.2 = false ∧ member.1.toNat < state.balances.data.size) →
      ∃ after, members.foldlM (applySyncReward reward proposerReward proposer) state = .ok after
  | [], state, _ => ⟨state, rfl⟩
  | member :: members, state, unsigned => by
    obtain ⟨absent, inside⟩ := unsigned member List.mem_cons_self
    have paid : applySyncReward reward proposerReward proposer state member =
        .ok (state.putBalance member.1.toNat inside
          (Uint64.saturatingSub state.balances.data[member.1.toNat] reward)) := by
      unfold applySyncReward
      simp only [absent, Bool.false_eq_true, ↓reduceIte]
      exact liftAccessor_ok.mpr (decreaseBalance_eq_ok_iff.mpr ⟨inside, rfl⟩)
    rw [List.foldlM_cons, paid]
    exact foldlM_applySyncReward_unsigned members _ fun other later =>
      ⟨(unsigned other (.tail _ later)).1, by
        simpa [BeaconState.putBalance] using (unsigned other (.tail _ later)).2⟩

/-- A key that a validator of the registry holds names an index of the registry. -/
private theorem validatorIndexOfPubkey_exists {state : BeaconState preset fork}
    {pubkey : BLSPubkey} (within : state.RegistryWithinLimit)
    (held : ∃ validator ∈ state.validators.data.toList, validator.pubkey = pubkey) :
    ∃ index, validatorIndexOfPubkey state pubkey = .ok index ∧
      index.toNat < state.validators.data.size := by
  unfold validatorIndexOfPubkey
  split
  · rename_i position located
    have there := (Array.findIdx?_eq_some_iff_getElem.mp located).1
    have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    unfold BeaconState.RegistryWithinLimit at within
    obtain ⟨index, named⟩ := Uint64.exists_toNat_eq (n := position) (by omega)
    refine ⟨index, ?_, by omega⟩
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff]
    exact Uint64.ofNatChecked_ok_iff.mpr ⟨by omega, named⟩
  · rename_i missing
    obtain ⟨validator, member, keyed⟩ := held
    have := Array.findIdx?_eq_none_iff.mp missing validator (by simpa using member)
    simp [keyed] at this

/-- From Altair, an empty sync aggregate with the signature of the point at infinity passes.

The state must hold the root of the slot before its own, and the reward must have a value.

Each key of the sync committee must be the key of a validator of the registry.

The registry must be within its limit, with one balance for each validator. -/
private theorem processSyncAggregate_none [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    {config : Config} {state : BeaconState preset fork} (altair : .altair ≤ fork)
    {aggregate : SyncAggregate preset}
    (none : ∀ bit ∈ aggregate.syncCommitteeBits.bits.toList, bit = false)
    (infinity : aggregate.syncCommitteeSignature = Signatures.G2_POINT_AT_INFINITY)
    (rooted : ∃ root, getBlockRootAtSlot state (Uint64.saturatingSub state.slot 1) = .ok root)
    (rewarded : ∃ reward, syncParticipantReward state = .ok reward)
    (keys : ∀ pubkey ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ validator ∈ state.validators.data.toList, validator.pubkey = pubkey)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state) :
    ∃ after, processSyncAggregate config .bls state altair aggregate = .ok after := by
  obtain ⟨root, rootOk⟩ := rooted
  obtain ⟨reward, rewardOk⟩ := rewarded
  obtain ⟨share, shareOk, -⟩ :=
    BlockLedger.syncProposerReward_of_participant rewardOk
  obtain ⟨domain, domained⟩ := getDomain_total config state DOMAIN_SYNC_COMMITTEE
    (some (computeEpochAtSlot preset (Uint64.saturatingSub state.slot 1)))
  obtain ⟨signingRoot, signed⟩ := computeSigningRoot_total root domain
  -- Each key of the committee names a validator of the registry.
  obtain ⟨members, membersOk, inside⟩ := mapM_exists_ok_forall
    (f := validatorIndexOfPubkey state)
    (holds := fun index : ValidatorIndex => index.toNat < state.validators.data.size)
    (state.currentSyncCommittee altair).value.pubkeys.toList
    fun pubkey member => validatorIndexOfPubkey_exists within (keys pubkey member)
  -- No member signed, so each pays its reward.
  obtain ⟨after, folded⟩ := foldlM_applySyncReward_unsigned (reward := reward)
    (proposerReward := share) (proposer := getBeaconProposerIndex state)
    (members.toArray.zip aggregate.syncCommitteeBits.bits.toArray).toList state
    fun ⟨index, bit⟩ listed => by
      have pair := List.of_mem_zip (by simpa using listed)
      unfold BalancesMatch at matched
      exact ⟨none bit (by simpa using pair.2), by rw [matched]; exact inside index pair.1⟩
  have arrayMembers : (state.currentSyncCommittee altair).value.pubkeys.toArray.mapM
      (validatorIndexOfPubkey state) = .ok members.toArray := by
    rw [Array.mapM_eq_mapM_toList]
    exact congrArg (List.toArray <$> ·) membersOk
  -- With no key, the signature of the point at infinity passes.
  have verified : ∀ message, syncAggregateVerify .bls #[] message
      aggregate.syncCommitteeSignature = true := fun message =>
    (syncAggregateVerify_empty (bls_fastAggregateVerify_empty _ _)).mpr infinity
  refine ⟨after, ?_⟩
  unfold processSyncAggregate
  simp only [syncParticipantPubkeys_none _ none, liftAccessor_ok.mpr domained,
    liftAccessor_ok.mpr rootOk, liftSsz_ok.mpr signed, verified, rewardOk, shareOk,
    arrayMembers, ensure, ↓reduceIte, bind, Except.bind]
  rw [← Array.foldlM_toList]
  exact folded

/-! ## The operations of an honest block -/

/-- From Altair until Gloas, an attestation step changes only balances and flags. -/
private theorem processAttestation_shape {checks : SignatureChecks} {parentSlot : Slot}
    {state after : BeaconState preset fork} {attestation : Attestation preset fork}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ balances previous current, after = { state with
      balances := balances, previousEpochParticipation := previous,
      currentEpochParticipation := current } := by
  rw [processAttestation_of_altair altair] at computed
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := computed
  split at final
  · rename_i gloas
    exact absurd beforeGloas (Nat.not_lt_of_le gloas)
  cases final
  obtain ⟨inside, -, rfl⟩ := increaseBalance_eq_ok_iff.mp raisedOk
  unfold setEpochParticipation
  split <;> exact ⟨_, _, _, rfl⟩

/-- From Altair until Gloas, the attestation steps change only balances and flags. -/
private theorem foldlM_processAttestation_shape {checks : SignatureChecks} {parentSlot : Slot}
    {state after : BeaconState preset fork} {attestations : List (Attestation preset fork)}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (computed : attestations.foldlM (processAttestation config checks · parentSlot ·) state =
      .ok after) :
    ∃ balances previous current, after = { state with
      balances := balances, previousEpochParticipation := previous,
      currentEpochParticipation := current } := by
  refine foldlM_ok_invariant (fun now : BeaconState preset fork => ∃ balances previous current,
    now = { state with
      balances := balances, previousEpochParticipation := previous,
      currentEpochParticipation := current }) ?_
    ⟨state.balances, state.previousEpochParticipation, state.currentEpochParticipation, rfl⟩
    computed
  rintro _ _ _ ⟨_, _, _, rfl⟩ ok
  obtain ⟨balances, previous, current, rfl⟩ := processAttestation_shape altair beforeGloas ok
  exact ⟨balances, previous, current, rfl⟩

/-- Before Gloas, the operations of an honest block are its attestation and deposit steps.

The block carries the deposits that the state expects, and its other lists are empty. -/
private theorem processOperations_honest
    {state input attested deposited : BeaconState preset fork}
    {key : Signatures.SecretKey} {block : BeaconBlock preset fork} {parentSlot : Slot}
    (honestBlock : HonestBlock config state key block) (beforeGloas : fork < .glamsterdam)
    (counted : ∀ before : fork < .hegota,
      expectedDepositCount input before = .ok (block.body.deposits before).data.size)
    (attestedOk : block.body.attestations.data.toList.foldlM
      (processAttestation config .bls · parentSlot ·) input = .ok attested)
    (depositedOk : ∀ before : fork < .hegota, (block.body.deposits before).data.toList.foldlM
      (processDeposit config .bls before) attested = .ok deposited) :
    processOperations config .bls input block.body parentSlot = .ok deposited := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  have attestedArray : block.body.attestations.data.foldlM
      (processAttestation config .bls · parentSlot ·) input = .ok attested := by
    rw [← Array.foldlM_toList]
    exact attestedOk
  have depositedArray : ∀ before : fork < .hegota, (block.body.deposits before).data.foldlM
      (processDeposit config .bls before) attested = .ok deposited := fun before => by
    rw [← Array.foldlM_toList]
    exact depositedOk before
  unfold processOperations
  simp only [notGloas, ↓reduceDIte, counted, honestBlock.proposerSlashings,
    honestBlock.attesterSlashings, honestBlock.voluntaryExits, Array.foldlM_empty, ensure,
    ↓reduceIte, bind, Except.bind, pure, Except.pure, attestedArray, depositedArray]
  -- From Capella the block carries no change of credentials.
  have changed : processBlsToExecutionChanges config .bls deposited block.body =
      .ok deposited := by
    unfold processBlsToExecutionChanges
    split
    · rename_i capella
      rw [honestBlock.changes capella]
      rfl
    · rfl
  rw [changed]
  dsimp only
  split
  -- From Electra the block carries no request of the execution layer.
  · rename_i electra
    obtain ⟨deposits, withdrawals, consolidations⟩ :=
      honestBlock.requests ⟨electra, beforeGloas⟩
    unfold processExecutionRequests
    simp only [deposits, withdrawals, consolidations, Array.foldlM_empty, bind, Except.bind, pure,
      Except.pure]
  · rfl

/-- From Altair until Gloas, the steps of an honest block pass when its attestation steps pass.

The attestation steps run on the state before the operations, which keeps what they read.

There they must pass, and leave a state with some property, such as flags of honest members.

The budget must leave room for the rewards of the proposer, one for each attestation.

The flags that the attestation steps set survive the deposits and the sync aggregate. -/
private theorem processBlock_honestBlock_of_attested [LawfulSszType (BeaconBlockBody preset fork)]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {state : BeaconState preset fork} {proposerKey : Signatures.SecretKey}
    {block : BeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (honestBlock : HonestBlock config state proposerKey block)
    (owned : ∃ validator, getValidator state block.proposerIndex = .ok validator ∧
      validator.pubkey = Signatures.skToPk proposerKey ∧ validator.slashed = false)
    (fresh : state.latestBlockHeader.slot < state.slot)
    (votesRoom : ∀ before : fork < .hegota, (state.eth1DataVotes before).data.size <
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (proven : ∀ (before : fork < .hegota) (position : Nat)
      (inside : position < (block.body.deposits before).data.size), ∃ leaf,
        hashTreeRoot (block.body.deposits before).data[position].data = .ok leaf ∧
        isValidMerkleBranch leaf (block.body.deposits before).data[position].proof.toList
          (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
          ((state.eth1DepositIndex before).toNat + position)
          (state.eth1Data before).depositRoot = true)
    (registryRoom : ∀ before : fork < .hegota, state.validators.data.size +
      (block.body.deposits before).data.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (pendingRoom : ∀ (electra : .pectra ≤ fork) (before : fork < .hegota),
      (state.pendingDeposits electra).data.size + (block.body.deposits before).data.size ≤
        preset.PENDING_DEPOSITS_LIMIT.toNat)
    (scores : InactivityScoresMatch state)
    (executes : ∀ headed, processBlockHeader state block = .ok headed →
      ∀ bellatrix : .bellatrix ≤ fork, ∃ executed,
        processBlockExecution config .bls engine headed block.body bellatrix = .ok executed)
    (syncKeys : ∀ pubkey ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ validator ∈ state.validators.data.toList, validator.pubkey = pubkey)
    (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    (room : budget + block.body.attestations.data.toList.length * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (depositRoom : fork < .pectra → ∀ before : fork < .hegota,
      budget + block.body.attestations.data.toList.length * (state.validators.data.size *
        (64 * preset.baseRewardCeiling) / 448) +
          ((block.body.deposits before).data.toList.map (·.data.amount.toNat)).sum < 2 ^ 64)
    (marks : BeaconState preset fork → Prop)
    (attests : ∀ input, AttestationReadsKept state input →
      getBeaconProposerIndex input = .ok block.proposerIndex →
      ∃ attested, block.body.attestations.data.toList.foldlM
        (processAttestation config .bls · state.latestBlockHeader.slot ·) input = .ok attested ∧
        marks attested) :
    ∃ after attested, marks attested ∧ processBlock config .bls engine state block = .ok after ∧
      ∀ current position, TargetFlagAt (recentParticipation attested altair current) position →
        TargetFlagAt (recentParticipation after altair current) position := by
  obtain ⟨proposer, found, pubkey, notSlashed⟩ := owned
  -- The steps before the operations pass, and keep what the attestations and deposits read.
  obtain ⟨input, computed, proposerI, kept, indexI, eth1I, pendingI, scoresI⟩ :=
    stateBeforeOperations_honestBlock_deposits beforeGloas apart honestBlock
      ⟨proposer, found, pubkey, notSlashed⟩ fresh votesRoom periodFits executes
  have holdsI := kept.budget _ _ holds
  have slotI := kept.slot
  have validatorsI := kept.validators
  -- The registry holds the proposer, so it is not empty.
  have proposerInside : block.proposerIndex.toNat < state.validators.data.size := by
    unfold getValidator at found
    split at found
    · rename_i located
      exact (Array.getElem?_eq_some_iff.mp located).1
    · cases found
  have participationI : ParticipationMatches input := fun altair => by
    rw [kept.previousParticipation, kept.currentParticipation, validatorsI]
    exact participation altair
  -- The attestation steps pass on the state before the operations.
  obtain ⟨attested, attestedOk, marked⟩ := attests input kept proposerI
  -- The attestation steps keep the budget, raised by one reward share for each attestation.
  obtain ⟨-, holdsA, participationA⟩ := foldlM_processAttestation_withinBudget
    (state := state) altair beforeGloas increment scaled (by omega) (spent := 0) validatorsI
    (by simpa using holdsI) participationI (by simpa using room) attestedOk
  rw [Nat.zero_add] at holdsA
  have matchedA : BalancesMatch attested := holdsA.matched
  obtain ⟨balances, previous, current, shaped⟩ :=
    foldlM_processAttestation_shape altair beforeGloas attestedOk
  -- The attestation steps keep the registry, the slot and the roots.
  have slotA : attested.slot = state.slot := by rw [shaped]; exact slotI
  have validatorsA : attested.validators = state.validators := by rw [shaped]; exact validatorsI
  have rootsA : attested.blockRoots = state.blockRoots := by rw [shaped]; exact kept.blockRoots
  -- They also keep what the deposits read.
  have indexA : attested.eth1DepositIndex = state.eth1DepositIndex := by
    rw [shaped]
    exact indexI
  have eth1A : ∀ before : fork < .hegota, attested.eth1Data before = state.eth1Data before := by
    rw [shaped]
    exact eth1I
  have pendingA : attested.pendingDeposits = state.pendingDeposits := by
    rw [shaped]
    exact pendingI
  have scoresA : InactivityScoresMatch attested := fun altair => by
    rw [shaped]
    show (input.inactivityScores altair).data.size = input.validators.data.size
    rw [scoresI, validatorsI]
    exact scores altair
  -- The deposit steps accept the deposits that are due, each with its proof.
  have before : fork < .hegota := Nat.lt_trans beforeGloas (by decide)
  have counted : ∀ before : fork < .hegota,
      expectedDepositCount input before = .ok (block.body.deposits before).data.size :=
    fun before => (kept.deposits before).trans (honestBlock.deposits before)
  have indexRoom := expectedDepositCount_index_lt (counted before)
  rw [indexI] at indexRoom
  obtain ⟨deposited, depositedOk, grownD⟩ := foldlM_processDeposit_exists_ok (config := config)
    (checks := .bls) before (deposits := (block.body.deposits before).data.toList)
    (state := attested)
    (fun position inside => by
      rw [indexA, eth1A before]
      simpa using proven before position (by simpa using inside))
    (by rw [indexA]; simpa using indexRoom)
    (by rw [validatorsA]; simpa using registryRoom before)
    (fun electra => by rw [pendingA]; simpa using pendingRoom electra before)
    (fun preElectra => by
      have := balanceSum_le_stakeSum matchedA
      have := holdsA.funded
      have := depositRoom preElectra before
      omega)
    matchedA participationA scoresA
  -- The other operations are empty, so the operations are the attestation and deposit steps.
  have operated := processOperations_honest (parentSlot := state.latestBlockHeader.slot)
    honestBlock beforeGloas counted attestedOk (fun _ => depositedOk)
  obtain ⟨frameD, belowD⟩ := foldlM_processDeposit_kept depositedOk
  -- The deposits keep the slot, the roots and the sync committee.
  have slotD : deposited.slot = state.slot := frameD.slot.trans slotA
  have rootsD : deposited.blockRoots = state.blockRoots := frameD.blockRoots.trans rootsA
  have syncD : deposited.currentSyncCommittee altair = state.currentSyncCommittee altair :=
    (processOperations_currentSyncCommittee altair operated).trans
      (congrFun kept.syncCommittee altair)
  -- The state is past its latest block, so the root of the slot before has a value.
  have rootedD : ∃ root,
      getBlockRootAtSlot deposited (Uint64.saturatingSub deposited.slot 1) = .ok root := by
    rw [getBlockRootAtSlot_congr slotD rootsD, slotD]
    have later := UInt64.lt_iff_toNat_lt.mp fresh
    have reach := roots.reach
    have two := roots.twoSlots
    have previousSlot := Uint64.toNat_saturatingSub state.slot 1
    rw [show (1 : UInt64).toNat = 1 from rfl] at previousSlot
    exact getBlockRootAtSlot_exists (by omega) (by omega) (by omega) (by omega)
  -- The reward reads the total active balance, which the deposits and attestations keep.
  have rewardedD : ∃ reward, syncParticipantReward deposited = .ok reward := by
    rw [BlockLedger.syncParticipantReward_congr (a := attested)
      (foldlM_processDeposit_getTotalActiveBalance depositedOk),
      BlockLedger.syncParticipantReward_congr (a := state) (by
        unfold getTotalActiveBalance getActiveValidatorIndicesChecked getTotalBalance
          getCurrentEpoch
        rw [validatorsA, slotA])]
    have slots : preset.SLOTS_PER_EPOCH ≠ 0 := fun zero => by
      have := roots.twoSlots
      rw [zero] at this
      simp at this
    exact syncParticipantReward_exists holds increment scaled incrementLe slots
      Uint64.ne_zero_of_neZero_toNat (by omega) (by omega)
  -- Each key of the sync committee stays the key of a validator, since the registry only grows.
  have keysD : ∀ pubkey ∈ (deposited.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ validator ∈ deposited.validators.data.toList, validator.pubkey = pubkey := by
    intro pubkey member
    rw [syncD] at member
    obtain ⟨validator, inside, keyed⟩ := syncKeys pubkey member
    have listed : pubkey ∈ validatorKeys attested := by
      unfold validatorKeys
      rw [validatorsA]
      exact List.mem_map.mpr ⟨validator, inside, keyed⟩
    exact List.mem_map.mp (frameD.pubkeysPrefix.subset listed)
  obtain ⟨after, synced⟩ := processSyncAggregate_none (config := config) altair
    (honestBlock.syncBits altair) (honestBlock.syncSignature altair) rootedD rewardedD keysD
    (by
      unfold BeaconState.RegistryWithinLimit
      have := registryRoom before
      rw [validatorsA] at grownD
      simp only [Array.length_toList] at grownD
      omega)
    (frameD.balancesMatch matchedA)
  refine ⟨after, attested, marked, ?_, ?_⟩
  · simp only [processBlock, altair, ↓reduceDIte, processBlockAltair, computed, operated, synced,
      bind, Except.bind]
  -- The deposits keep the flags of the registry before them, and the sync aggregate every flag.
  · intro current position flag
    obtain ⟨flags, found, set⟩ := flag
    have sized := participationA altair
    have below : position < attested.validators.data.size := by
      have := (Array.getElem?_eq_some_iff.mp found).1
      unfold recentParticipation at this
      split at this <;> omega
    have same := belowD altair position below
    obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
    refine ⟨flags, ?_, set⟩
    unfold recentParticipation at found ⊢
    by_cases currentEpoch : current = true
    · rw [ite_eq_left currentEpoch] at found ⊢
      rw [same.2]
      exact found
    · rw [ite_eq_right currentEpoch] at found ⊢
      rw [same.1]
      exact found

/-- From Altair until Gloas, the steps of an honest block with honest attestations pass.

The block is that of the proposer of the slot, built with its key on the state at the slot.

Each honest member of each committee then holds the timely target flag of its target epoch.

That needs the state to hold the target root for the first slot of that epoch.

It needs these facts:

- The proposer and each validator of the honest set hold the public keys of their secret keys.
- The proposer must not be slashed, and the state must hold no block at its slot yet.
- Before Heze the votes on the deposit contract must leave room for one more in the period.
- The block carries as many deposits as the state expects.
- Each comes with a Merkle proof to the deposit root of the state, at its index.
  That proof is an input.
- The registry, and from Electra the pending deposits, must have room for each deposit.
- Before Electra the budget must leave room for the amounts after the rewards of the proposer.
- From Altair the inactivity scores hold one entry for each validator.
- The execution part of the block must pass on the state after its header, an assumption.
- Each key of the current sync committee must be the key of a validator.
- The attestations are built on the state at the slot, with the checks of the attestation step.
- The secret keys of the honest members of each committee must not sum to zero.
- The state must be within a budget, with room for the rewards of the proposer.
- The buffer of block roots must reach the previous epoch, and the slot plus its length must fit.
- The voting period on the deposit contract must fit in 64 bits.
- One increment must be at most the largest effective balance, so that the sync reward fits.
- The sync committee must not be empty.
- The mixes must span more than the seed lookahead plus two epochs.
- The encoding of a block body must be lawful, so that the body has a root.
-/
theorem processBlock_honestBlock [LawfulSszType (BeaconBlockBody preset fork)]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {state : BeaconState preset fork} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork}
    (honestBlock : HonestBlock config state (key block.proposerIndex) block)
    (registered : ∀ index ∈ insert block.proposerIndex honest, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (unslashed : ∀ validator, getValidator state block.proposerIndex = .ok validator →
      validator.slashed = false)
    (fresh : state.latestBlockHeader.slot < state.slot)
    (votesRoom : ∀ before : fork < .hegota, (state.eth1DataVotes before).data.size <
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (proven : ∀ (before : fork < .hegota) (position : Nat)
      (inside : position < (block.body.deposits before).data.size), ∃ leaf,
        hashTreeRoot (block.body.deposits before).data[position].data = .ok leaf ∧
        isValidMerkleBranch leaf (block.body.deposits before).data[position].proof.toList
          (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
          ((state.eth1DepositIndex before).toNat + position)
          (state.eth1Data before).depositRoot = true)
    (registryRoom : ∀ before : fork < .hegota, state.validators.data.size +
      (block.body.deposits before).data.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (pendingRoom : ∀ (electra : .pectra ≤ fork) (before : fork < .hegota),
      (state.pendingDeposits electra).data.size + (block.body.deposits before).data.size ≤
        preset.PENDING_DEPOSITS_LIMIT.toNat)
    (scores : InactivityScoresMatch state)
    (executes : ∀ headed, processBlockHeader state block = .ok headed →
      ∀ bellatrix : .bellatrix ≤ fork, ∃ executed,
        processBlockExecution config .bls engine headed block.body bellatrix = .ok executed)
    (syncKeys : ∀ pubkey ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ validator ∈ state.validators.data.toList, validator.pubkey = pubkey)
    (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    {votes : List (AttestationData × CommitteeIndex)}
    (room : budget + votes.length * (state.validators.data.size *
      (64 * preset.baseRewardCeiling) / 448) +
        state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (depositRoom : fork < .pectra → ∀ before : fork < .hegota, budget + votes.length *
      (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) +
        ((block.body.deposits before).data.toList.map (·.data.amount.toNat)).sum < 2 ^ 64)
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
    (sum : ∀ vote ∈ votes, ∀ committee,
      getBeaconCommittee state vote.1.slot vote.2 = .ok committee →
        (((honestSigners honest committee).map key).map (·.val)).sum ≠ 0)
    (built : List.Forall₂ (fun vote attestation =>
      honestAttestation config state honest key vote.1 vote.2 = .ok attestation)
        votes block.body.attestations.data.toList) :
    ∃ after, processBlock config .bls engine state block = .ok after ∧
      ∀ vote ∈ votes, getBlockRoot state vote.1.target.epoch = .ok vote.1.target.root →
        ∀ committee, getBeaconCommittee state vote.1.slot vote.2 = .ok committee →
          ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation after altair
            (vote.1.target.epoch == getCurrentEpoch state)) index.toNat := by
  obtain ⟨proposer, found, pubkey⟩ := registered block.proposerIndex (Finset.mem_insert_self _ _)
  have lengths : block.body.attestations.data.toList.length = votes.length :=
    built.length_eq.symm
  obtain ⟨after, attested, marked, processed, carried⟩ := processBlock_honestBlock_of_attested
    altair beforeGloas apart honestBlock ⟨proposer, found, pubkey, unslashed _ found⟩ fresh
    votesRoom periodFits proven registryRoom pendingRoom scores executes syncKeys roots slotRoom
    increment scaled incrementLe holds participation (by rw [lengths]; exact room)
    (fun preElectra before => by rw [lengths]; exact depositRoom preElectra before)
    (fun attested => ∀ vote ∈ votes,
      getBlockRoot state vote.1.target.epoch = .ok vote.1.target.root →
        ∀ committee, getBeaconCommittee state vote.1.slot vote.2 = .ok committee →
          ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation attested altair
            (vote.1.target.epoch == getCurrentEpoch state)) index.toNat)
    -- The steps before the operations keep every value that the attestations read.
    fun input kept proposerI => by
      have holdsI := kept.budget _ _ holds
      have slotI := kept.slot
      have validatorsI := kept.validators
      have currentI : getCurrentEpoch input = getCurrentEpoch state := by
        unfold getCurrentEpoch
        rw [slotI]
      have previousI : getPreviousEpoch input = getPreviousEpoch state := by
        unfold getPreviousEpoch
        rw [currentI]
      -- The registry holds the proposer, so it is not empty.
      have proposerInside : block.proposerIndex.toNat < state.validators.data.size := by
        unfold getValidator at found
        split at found
        · rename_i located
          exact (Array.getElem?_eq_some_iff.mp located).1
        · cases found
      -- Each vote is for a slot of the previous or the current epoch.
      have bounds : ∀ vote ∈ votes,
          getPreviousEpoch state ≤ computeEpochAtSlot preset vote.1.slot ∧
            computeEpochAtSlot preset vote.1.slot ≤ getCurrentEpoch state := by
        intro vote member
        rw [← slotEpoch vote member]
        have := getPreviousEpoch_le state
        rcases recent vote member with same | same <;> rw [same]
        · exact ⟨UInt64.le_refl _, this⟩
        · exact ⟨this, UInt64.le_refl _⟩
      -- The committees of each vote are the same on both states.
      have committeesI : ∀ vote ∈ votes, ∀ index,
          getBeaconCommittee input vote.1.slot index = getBeaconCommittee state vote.1.slot index :=
        fun vote member index =>
          kept.committees _ (bounds vote member).1 (bounds vote member).2 _ index rfl
      -- The honest attestations built on the state are those built on the input state.
      have builtI : List.Forall₂ (fun vote attestation =>
          honestAttestation config input honest key vote.1 vote.2 = .ok attestation)
            votes block.body.attestations.data.toList :=
        forall₂_imp_of_mem built fun vote _ member made => by
          rw [honestAttestation_eq_of_kept kept (bounds vote member).1 (bounds vote member).2]
          exact made
      have participationI : ParticipationMatches input := fun altair => by
        rw [kept.previousParticipation, kept.currentParticipation, validatorsI]
        exact participation altair
      -- The attestation steps accept them on the input state, which reads the same values.
      obtain ⟨attested, attestedOk, flagged⟩ := foldlM_processAttestation_honestAttestation
        (state := input) altair beforeGloas (honest := honest) (key := key)
        state.latestBlockHeader.slot roots (by rw [slotI]; exact slotRoom) increment scaled holdsI
        participationI (by rw [validatorsI]; exact room)
        (fun vote member => by rw [previousI, currentI]; exact recent vote member) slotEpoch
        (fun vote member => by rw [slotI]; exact past vote member)
        (fun vote member => by rw [slotI]; exact early vote member)
        (fun vote member => by rw [slotI]; exact deadline vote member) indexed
        (fun vote member => by
          unfold getCommitteeCountPerSlot getActiveValidatorIndices
          rw [validatorsI]
          exact below vote member)
        (fun vote member => by
          rw [currentI, kept.currentJustified, kept.previousJustified]
          exact source vote member)
        (fun index member => by
          unfold getValidator
          rw [validatorsI]
          exact registered index (Finset.mem_insert_of_mem member))
        (fun vote member committee => by
          rw [committeesI vote member]
          exact sum vote member committee)
        ⟨block.proposerIndex, proposerI, by rw [validatorsI]; exact proposerInside⟩ builtI
      refine ⟨attested, attestedOk, fun vote member rooted committee committeeOk index inside
        honestIndex => ?_⟩
      have flag := flagged vote member
        (by simp only [getBlockRoot, getBlockRootAtSlot_congr slotI kept.blockRoots]; exact rooted)
        committee (by rw [committeesI vote member]; exact committeeOk) index inside honestIndex
      rw [currentI] at flag
      exact flag
  -- The deposit steps accept the deposits, and keep the flags that the attestations set.
  exact ⟨after, processed, fun vote member rooted committee committeeOk index inside honestIndex =>
    carried _ _ (marked vote member rooted committee committeeOk index inside honestIndex)⟩

/-- From Electra until Gloas, the steps of an honest block with honest slot aggregates pass.

Each aggregate covers the committees of a slot that have an honest member, built on the state.

The block and the state meet the conditions of an honest block, except those on its attestations.

The execution part of the block must pass on the state after its header, an assumption.

Each deposit has a Merkle proof to the deposit root of the state, at its index.

That proof is an input.

The data of each aggregate meet the checks of the attestation step, with committee index zero.

The secret keys of the honest members of the committees of each slot must not sum to zero.

The active validators times the committees of each epoch must fit in 64 bits.

Each honest member of each committee of each slot then holds the timely target flag.

That needs the state to hold the target root for the first slot of the target epoch. -/
theorem processBlock_honestBlock_honestSlotAggregate [LawfulSszType (BeaconBlockBody preset fork)]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {budget scoreBound : Nat}
    (electra : .pectra ≤ fork) (beforeGloas : fork < .glamsterdam)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {state : BeaconState preset fork} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork}
    (honestBlock : HonestBlock config state (key block.proposerIndex) block)
    (registered : ∀ index ∈ insert block.proposerIndex honest, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (unslashed : ∀ validator, getValidator state block.proposerIndex = .ok validator →
      validator.slashed = false)
    (fresh : state.latestBlockHeader.slot < state.slot)
    (votesRoom : ∀ before : fork < .hegota, (state.eth1DataVotes before).data.size <
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (proven : ∀ (before : fork < .hegota) (position : Nat)
      (inside : position < (block.body.deposits before).data.size), ∃ leaf,
        hashTreeRoot (block.body.deposits before).data[position].data = .ok leaf ∧
        isValidMerkleBranch leaf (block.body.deposits before).data[position].proof.toList
          (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
          ((state.eth1DepositIndex before).toNat + position)
          (state.eth1Data before).depositRoot = true)
    (registryRoom : ∀ before : fork < .hegota, state.validators.data.size +
      (block.body.deposits before).data.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (pendingRoom : ∀ before : fork < .hegota,
      (state.pendingDeposits electra).data.size + (block.body.deposits before).data.size ≤
        preset.PENDING_DEPOSITS_LIMIT.toNat)
    (scores : InactivityScoresMatch state)
    (executes : ∀ headed, processBlockHeader state block = .ok headed →
      ∀ bellatrix : .bellatrix ≤ fork, ∃ executed,
        processBlockExecution config .bls engine headed block.body bellatrix = .ok executed)
    (syncKeys : ∀ pubkey ∈
        (state.currentSyncCommittee (Nat.le_trans (by decide) electra)).value.pubkeys.toList,
      ∃ validator ∈ state.validators.data.toList, validator.pubkey = pubkey)
    (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    {datas : List AttestationData}
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
    (sum : ∀ data ∈ datas, ∀ committees, (List.range
        (getCommitteeCountPerSlot state data.target.epoch).toNat).mapM
      (fun position => getBeaconCommittee state data.slot position.toUInt64) = .ok committees →
        (((committees.flatMap (honestSigners honest)).map key).map (·.val)).sum ≠ 0)
    (built : List.Forall₂ (fun data attestation =>
      honestSlotAggregate electra config state honest key data = .ok attestation)
        datas block.body.attestations.data.toList) :
    ∃ after, processBlock config .bls engine state block = .ok after ∧
      ∀ data ∈ datas, getBlockRoot state data.target.epoch = .ok data.target.root →
        ∀ committeeIndex committee,
          committeeIndex < getCommitteeCountPerSlot state data.target.epoch →
          getBeaconCommittee state data.slot committeeIndex = .ok committee →
            ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation after
              (Nat.le_trans (by decide) electra) (data.target.epoch == getCurrentEpoch state))
                index.toNat := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  obtain ⟨proposer, found, pubkey⟩ := registered block.proposerIndex (Finset.mem_insert_self _ _)
  have lengths : block.body.attestations.data.toList.length = datas.length :=
    built.length_eq.symm
  obtain ⟨after, attested, marked, processed, carried⟩ := processBlock_honestBlock_of_attested
    altair beforeGloas apart honestBlock ⟨proposer, found, pubkey, unslashed _ found⟩ fresh
    votesRoom periodFits proven registryRoom (fun _ before => pendingRoom before) scores
    executes syncKeys roots slotRoom increment scaled incrementLe holds participation
    (by rw [lengths]; exact room)
    (fun preElectra => absurd electra (Nat.not_le_of_lt preElectra))
    (fun attested => ∀ data ∈ datas,
      getBlockRoot state data.target.epoch = .ok data.target.root →
        ∀ committeeIndex committee,
          committeeIndex < getCommitteeCountPerSlot state data.target.epoch →
          getBeaconCommittee state data.slot committeeIndex = .ok committee →
            ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation attested
              altair (data.target.epoch == getCurrentEpoch state)) index.toNat)
    fun input kept proposerI => by
      have holdsI := kept.budget _ _ holds
      have slotI := kept.slot
      have validatorsI := kept.validators
      have currentI : getCurrentEpoch input = getCurrentEpoch state := by
        unfold getCurrentEpoch
        rw [slotI]
      have previousI : getPreviousEpoch input = getPreviousEpoch state := by
        unfold getPreviousEpoch
        rw [currentI]
      -- The registry holds the proposer, so it is not empty.
      have proposerInside : block.proposerIndex.toNat < state.validators.data.size := by
        unfold getValidator at found
        split at found
        · rename_i located
          exact (Array.getElem?_eq_some_iff.mp located).1
        · cases found
      -- Each aggregate is for a slot of the previous or the current epoch.
      have bounds : ∀ data ∈ datas,
          getPreviousEpoch state ≤ computeEpochAtSlot preset data.slot ∧
            computeEpochAtSlot preset data.slot ≤ getCurrentEpoch state := by
        intro data member
        rw [← slotEpoch data member]
        have := getPreviousEpoch_le state
        rcases recent data member with same | same <;> rw [same]
        · exact ⟨UInt64.le_refl _, this⟩
        · exact ⟨this, UInt64.le_refl _⟩
      -- The committees of each slot, and their count, are the same on both states.
      have committeesI : ∀ data ∈ datas, ∀ index,
          getBeaconCommittee input data.slot index = getBeaconCommittee state data.slot index :=
        fun data member index =>
          kept.committees _ (bounds data member).1 (bounds data member).2 _ index rfl
      have activeI : ∀ epoch,
          getActiveValidatorIndices input epoch = getActiveValidatorIndices state epoch := by
        intro epoch
        unfold getActiveValidatorIndices
        rw [validatorsI]
      have countI : ∀ epoch,
          getCommitteeCountPerSlot input epoch = getCommitteeCountPerSlot state epoch := by
        intro epoch
        unfold getCommitteeCountPerSlot
        rw [activeI]
      -- The honest aggregates built on the state are those built on the input state.
      have builtI : List.Forall₂ (fun data attestation =>
          honestSlotAggregate electra config input honest key data = .ok attestation)
            datas block.body.attestations.data.toList :=
        forall₂_imp_of_mem built fun data _ member made => by
          rw [honestSlotAggregate_eq_of_kept electra kept (bounds data member).1
            (bounds data member).2]
          exact made
      have participationI : ParticipationMatches input := fun altair => by
        rw [kept.previousParticipation, kept.currentParticipation, validatorsI]
        exact participation altair
      -- The attestation steps accept them on the input state, which reads the same values.
      obtain ⟨attested, attestedOk, flagged⟩ := foldlM_processAttestation_honestSlotAggregate
        (state := input) electra beforeGloas (honest := honest) (key := key)
        state.latestBlockHeader.slot roots (by rw [slotI]; exact slotRoom) increment scaled
        holdsI participationI (by rw [validatorsI]; exact room)
        (fun data member => by rw [previousI, currentI]; exact recent data member) slotEpoch
        (fun data member => by rw [slotI]; exact past data member)
        (fun data member => by rw [slotI]; exact early data member) indexed
        (fun data member => by rw [activeI, countI]; exact shuffleRoom data member)
        (fun data member => by
          rw [currentI, kept.currentJustified, kept.previousJustified]
          exact source data member)
        (fun index member => by
          unfold getValidator
          rw [validatorsI]
          exact registered index (Finset.mem_insert_of_mem member))
        (fun data member committees committeesOk => by
          rw [countI] at committeesOk
          simp only [committeesI data member] at committeesOk
          exact sum data member committees committeesOk)
        ⟨block.proposerIndex, proposerI, by rw [validatorsI]; exact proposerInside⟩ builtI
      refine ⟨attested, attestedOk, fun data member rooted committeeIndex committee below
        committeeOk index inside honestIndex => ?_⟩
      have flag := flagged data member
        (by simp only [getBlockRoot, getBlockRootAtSlot_congr slotI kept.blockRoots]; exact rooted)
        committeeIndex committee (by rw [countI]; exact below)
        (by rw [committeesI data member]; exact committeeOk) index inside honestIndex
      rw [currentI] at flag
      exact flag
  exact ⟨after, processed, fun data member rooted committeeIndex committee below committeeOk index
    inside honestIndex => carried _ _
      (marked data member rooted committeeIndex committee below committeeOk index inside
        honestIndex)⟩

/-- A block at the slot of a state that passes its steps also passes them with both checks.

The proposer sets its state root to the root of the state after it, then signs it.

The block then passes the step of a run, which checks the signature and the state root.

The proposer must hold the public key of the secret key that signs.

The encoding of a beacon state must be lawful, so that the state after the block has a root. -/
theorem applySignedBlock_of_processBlock [LawfulSszType (BeaconState preset fork)]
    {state after : BeaconState preset fork} {key : Signatures.SecretKey}
    {block : BeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (slot : block.slot = state.slot)
    (owned : ∃ validator, getValidator state block.proposerIndex = .ok validator ∧
      validator.pubkey = Signatures.skToPk key)
    (processed : processBlock config .bls engine state block = .ok after) :
    ∃ root signature, hashTreeRoot after = .ok root ∧
      getBlockSignature config state { block with stateRoot := root } key = .ok signature ∧
      applySignedBlock config .bls engine state ⟨{ block with stateRoot := root }, signature⟩
        true = .ok after := by
  obtain ⟨validator, found, pubkey⟩ := owned
  -- The header step computes the root of the body of the block.
  obtain ⟨input, last, ⟨_, headed, _, _, _, headerOk, _⟩, _⟩ :=
    processBlock_operationsInput processed
  obtain ⟨bodyRoot, bodied, -⟩ := processBlockHeader_eq headerOk
  obtain ⟨root, rooted⟩ := hashTreeRoot_total after
  -- The block has the root of its header, so its signing root has a value.
  obtain ⟨headerRoot, headerRooted⟩ := hashTreeRoot_total
    (BeaconBlockHeader.mk block.slot block.proposerIndex block.parentRoot root bodyRoot)
  obtain ⟨domain, domained⟩ := getDomain_total config state DOMAIN_BEACON_PROPOSER
    (some (computeEpochAtSlot preset block.slot))
  obtain ⟨signingRoot, signingRooted⟩ := hashTreeRoot_total (SigningData.mk headerRoot domain)
  have signingOk : computeSigningRoot { block with stateRoot := root } domain =
      .ok signingRoot := by
    unfold computeSigningRoot
    rw [← BeaconBlock.hashTreeRoot_header (block := { block with stateRoot := root }) bodied,
      headerRooted]
    exact signingRooted
  obtain ⟨signature, made⟩ := Signatures.sign_ok key (packBytes signingRoot)
  have signatureOk : getBlockSignature config state { block with stateRoot := root } key =
      .ok signature := by
    rw [getBlockSignature, signAtEpoch, domained, mapError_ok_bind, signingOk, mapError_ok_bind,
      made]
    rfl
  -- The proposer verifies the signature, at the epoch of the state.
  have verified := verifyBlockSignature_of_getBlockSignature
    (signed := ⟨{ block with stateRoot := root }, signature⟩) found pubkey
    (by rw [slot]; rfl) signatureOk
  -- The block steps never read the state root of the block.
  have same : processBlock config .bls engine state { block with stateRoot := root } =
      processBlock config .bls engine state block := rfl
  refine ⟨root, signature, rooted, signatureOk, ?_⟩
  unfold applySignedBlock checkBlockSignature checkStateRoot
  simp only [verified, same, processed, rooted, liftSsz, Except.mapError, ensure, bind,
    Except.bind, pure, Except.pure, ↓reduceIte]

end EthLib.Consensus
