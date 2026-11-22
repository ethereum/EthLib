module

public import EthLib.Consensus.Proofs.HonestBlock
public import EthLib.Consensus.Proofs.LivenessContinuation

/-!
# Proofs: an honest proposer gathers the target votes of the slots shortly before it

An honest proposer at a slot carries the honest votes of the recent slots of its epoch.

Those are the slots of the current epoch before its own, by at most a gap.

Before Electra it carries one attestation for each committee of those slots with an honest member.

From Electra it carries one aggregate for each of those slots with an honest member.

The gap must leave room for them in the block.

Each vote heads the latest block at its slot or before.

It targets the latest block at the first slot of the epoch or before.

Its source is the current justified checkpoint.

The rest of the block is free: the proposer may complete it as an honest block.

That its payload passes and its deposits have proofs is an assumption.

It is on the execution layer and on the deposit data.

Then the block passes the step of a run, and it gives each of those honest members the flag.

Each vote it carries is an honest vote on the state before it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config}

/-- The conditions on a state for its honest proposer to carry the votes of the gap before it.

The honest validators hold their keys in the registry, and the proposer is not slashed.

The state is within a budget, and its flags and scores match its registry.

The deposit votes leave room for one more, and the members of the sync committee are registered.

Every slot up to the end of the buffer of roots fits in 64 bits.

The budget leaves room for the rewards of a full block of attestations.

The active validators times the committees of the epoch fit in 64 bits.

Each committee of the epoch has at most the largest size of a committee, an assumption.

The gap times the attestations of a slot fit in a block.

The secret keys of the honest signers of each attestation must not sum to zero, an assumption.

Any list of attestations that fits in a block completes to an honest block of the proposer.

That is an assumption, on the execution layer and on the deposit data.

Its execution part passes, its deposits have proofs, and the registry has room for them.

The pending deposits have room for them, and before Electra the budget has room for their amounts.
-/
structure ProposalConditions (config : Config) (honest : Finset ValidatorIndex)
    (key : ValidatorIndex → Signatures.SecretKey) (budget scoreBound gap : Nat)
    (state : BeaconState preset fork) (proposer : ValidatorIndex) : Prop where
  /-- Each honest validator holds the public key of its secret key. -/
  registered : ∀ index ∈ honest, ∃ validator,
    getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index)
  /-- The proposer is not slashed. -/
  unslashed : ∀ validator, getValidator state proposer = .ok validator →
    validator.slashed = false
  /-- The state is within the budget. -/
  holds : WithinBudget budget scoreBound state
  /-- The flags of participation match the registry. -/
  participation : ParticipationMatches state
  /-- The inactivity scores match the registry. -/
  scores : InactivityScoresMatch state
  /-- Before Heze, the votes on the deposit contract leave room for one more. -/
  votesRoom : ∀ before : fork < .hegota, (state.eth1DataVotes before).data.size <
    preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat
  /-- From Altair, each key of the current sync committee is in the registry. -/
  syncKeys : ∀ altair : .altair ≤ fork,
    ∀ pubkey ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ validator ∈ state.validators.data.toList, validator.pubkey = pubkey
  /-- The slot plus the length of the buffer of roots fits in 64 bits. -/
  slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64
  /-- The budget leaves room for the rewards of a full block of attestations. -/
  room : budget + (parameters preset fork).MAX_ATTESTATIONS.toNat *
      (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) +
    state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64
  /-- The active validators times the committees of the current epoch fit in 64 bits. -/
  shuffleRoom : (getActiveValidatorIndices state (getCurrentEpoch state)).length *
    ((getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat *
      preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64
  /-- Each committee of the current epoch has at most the largest size of a committee. -/
  committeeSizes : ∀ (slot : Slot) (index : CommitteeIndex) committee,
    computeEpochAtSlot preset slot = getCurrentEpoch state →
    index < getCommitteeCountPerSlot state (getCurrentEpoch state) →
    getBeaconCommittee state slot index = .ok committee →
      committee.size ≤ preset.MAX_VALIDATORS_PER_COMMITTEE.toNat
  /-- The gap times the attestations of one slot fit in a block. -/
  capacity : gap * (if .pectra ≤ fork then 1
      else (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat) ≤
    (parameters preset fork).MAX_ATTESTATIONS.toNat
  /-- Before Electra, the honest keys of a committee of the gap do not sum to zero. -/
  committeeKeys : ¬.pectra ≤ fork → ∀ (slot : Slot) (index : CommitteeIndex) committee,
    computeEpochAtSlot preset slot = getCurrentEpoch state → slot < state.slot →
    state.slot.toNat ≤ slot.toNat + gap →
    index < getCommitteeCountPerSlot state (getCurrentEpoch state) →
    getBeaconCommittee state slot index = .ok committee → honestSigners honest committee ≠ [] →
      (((honestSigners honest committee).map key).map (·.val)).sum ≠ 0
  /-- From Electra, the keys of the honest members of a slot of the gap do not sum to zero. -/
  slotKeys : .pectra ≤ fork → ∀ (slot : Slot) committees,
    computeEpochAtSlot preset slot = getCurrentEpoch state → slot < state.slot →
    state.slot.toNat ≤ slot.toNat + gap →
    (List.range (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat).mapM
      (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees →
    committees.flatMap (honestSigners honest) ≠ [] →
      (((committees.flatMap (honestSigners honest)).map key).map (·.val)).sum ≠ 0
  /-- Any list of attestations that fits completes to an honest block of the proposer.

  Its execution part passes on the state after its header, and its deposits have proofs.

  The registry and the pending deposits have room for its deposits.

  Before Electra, the budget after the rewards of a full block has room for their amounts. -/
  complete : ∀ attestations : List (Attestation preset fork),
    attestations.length ≤ (parameters preset fork).MAX_ATTESTATIONS.toNat →
    ∃ (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork),
      HonestBlock config state (key proposer) block ∧
      block.body.attestations.data.toList = attestations ∧
      (∀ headed, processBlockHeader state block = .ok headed →
        ∀ bellatrix : .bellatrix ≤ fork, ∃ executed,
          processBlockExecution config .bls engine headed block.body bellatrix = .ok executed) ∧
      (∀ (before : fork < .hegota) (position : Nat)
        (inside : position < (block.body.deposits before).data.size), ∃ leaf,
          hashTreeRoot (block.body.deposits before).data[position].data = .ok leaf ∧
          isValidMerkleBranch leaf (block.body.deposits before).data[position].proof.toList
            (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
            ((state.eth1DepositIndex before).toNat + position)
            (state.eth1Data before).depositRoot = true) ∧
      (∀ before : fork < .hegota, state.validators.data.size +
        (block.body.deposits before).data.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat) ∧
      (∀ (electra : .pectra ≤ fork) (before : fork < .hegota),
        (state.pendingDeposits electra).data.size + (block.body.deposits before).data.size ≤
          preset.PENDING_DEPOSITS_LIMIT.toNat) ∧
      (fork < .pectra → ∀ before : fork < .hegota,
        budget + (parameters preset fork).MAX_ATTESTATIONS.toNat *
          (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) +
        ((block.body.deposits before).data.toList.map (·.data.amount.toNat)).sum < 2 ^ 64)

/-! ## The slots of the gap -/

/-- The slots of the current epoch before the slot of a state, by at most a gap, form a list.

The list has at most the gap as length. -/
private theorem exists_window (state : BeaconState preset fork) (gap : Nat)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    ∃ window : List Slot, (∀ slot, slot ∈ window ↔
      computeEpochAtSlot preset slot = getCurrentEpoch state ∧ slot < state.slot ∧
        state.slot.toNat ≤ slot.toNat + gap) ∧ window.length ≤ gap := by
  set S := state.slot.toNat with hS
  set P := preset.SLOTS_PER_EPOCH.toNat with hP
  set low := max (S / P * P) (S - gap) with hlow
  refine ⟨(List.range' low (S - low)).map Nat.toUInt64, fun slot => ?_, by simp; omega⟩
  have small : S < 2 ^ 64 := UInt64.toNat_lt _
  have epochIff : computeEpochAtSlot preset slot = getCurrentEpoch state ↔
      slot.toNat / P = S / P := by
    rw [getCurrentEpoch, computeEpochAtSlot, computeEpochAtSlot, ← UInt64.toNat_inj,
      UInt64.toNat_div, UInt64.toNat_div]
  rw [epochIff, UInt64.lt_iff_toNat_lt, List.mem_map]
  have lowLe : S / P * P ≤ S := Nat.div_mul_le_self S P
  constructor
  · rintro ⟨a, member, rfl⟩
    rw [List.mem_range'_1] at member
    have aSmall : a < 2 ^ 64 := by omega
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' aSmall]
    refine ⟨Nat.le_antisymm (Nat.div_le_div_right (by omega)) ?_, by omega, by omega⟩
    exact (Nat.le_div_iff_mul_le positive).mpr (by omega)
  · rintro ⟨same, before, within⟩
    refine ⟨slot.toNat, List.mem_range'_1.mpr ⟨?_, by omega⟩, by simp⟩
    have := Nat.div_mul_le_self slot.toNat P
    rw [same] at this
    omega

/-! ## The committees of a slot -/

/-- The committees of a slot all have values, when one of them has a member.

The active validators times the committees of the epoch of the slot must fit in 64 bits. -/
private theorem committees_exists_ok {state : BeaconState preset fork} {slot : Slot}
    {index : CommitteeIndex} {members : Array ValidatorIndex} {member : ValidatorIndex}
    (committeeOk : getBeaconCommittee state slot index = .ok members) (seated : member ∈ members)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (room : (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length *
      ((getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64) :
    ∃ committees, (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).mapM
      (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees := by
  obtain ⟨active, shuffled, shuffleOk⟩ := attesterShuffle_ok_of_getBeaconCommittee committeeOk
  obtain ⟨seed, -, activeEq⟩ := attesterShuffle_ok shuffleOk
  -- The member is active, so the count of committees alone fits in 64 bits.
  have nonempty : 0 < (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length :=
    List.length_pos_of_mem (mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk seated)
  have countFits : (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ nonempty) room
  refine mapM_exists_ok fun position listed => ?_
  have below := toUInt64_lt_of_lt (List.mem_range.mp listed)
  simp only [getBeaconCommittee, shuffleOk, bind, Except.bind]
  exact beaconCommitteeOf_ok_of_lt positive countFits
    (by simpa only [activeEq, List.size_toArray] using room) below

/-! ## The signed block -/

/-- A block of an honest proposer whose steps pass is signed into an honest step of a run.

Each vote that it carries must be an honest vote, and it must gather the votes of the gap. -/
private theorem exists_signed_of_processBlock [LawfulSszType (BeaconState preset fork)]
    {gap : Nat} {state after : BeaconState preset fork} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork}
    (honestProposer : block.proposerIndex ∈ honest)
    (honestBlock : HonestBlock config state (key block.proposerIndex) block)
    (owned : ∃ validator, getValidator state block.proposerIndex = .ok validator ∧
      validator.pubkey = Signatures.skToPk (key block.proposerIndex))
    (notDue : upgradeDue config ⟨fork, state⟩ = false)
    (processed : processBlock config .bls engine state block = .ok after)
    (votes : ∀ vote ∈ blockVotes state block, HonestVote honest state vote)
    (gathers : GathersVotes honest gap state after) :
    ∃ (after : BeaconState preset fork) (engine : ExecutionEngine preset fork)
      (signed : SignedBeaconBlock preset fork) (due : upgradeDue config ⟨fork, state⟩ = false)
      (ok : applySignedBlock config .bls engine state signed true = .ok after),
      (Step.block engine signed due ok).Honest config honest key ∧
        GathersVotes honest gap state after := by
  obtain ⟨root, signature, -, -, applied⟩ :=
    applySignedBlock_of_processBlock honestBlock.slot owned processed
  -- The block steps read no state root, so the signed block is honest too.
  have signedHonest : HonestBlock config state (key block.proposerIndex)
      { block with stateRoot := root } := by
    cases honestBlock
    constructor <;> assumption
  exact ⟨after, engine, _, notDue, applied, ⟨honestProposer, signedHonest, votes⟩, gathers⟩

/-- From Altair until Gloas, an honest proposer gathers the votes of the gap before its slot.

The proposer of the slot of the state is honest, and the slot is after the latest block header.

No upgrade is due at the state, and it meets the conditions of a proposal.

The ring of mixes spans more than the seed lookahead plus two epochs.

The voting period on the deposit contract fits in 64 bits.

An epoch has two slots at least, and the buffer of roots reaches the previous epoch.

The balance increment is nonzero and at most the largest effective balance.

The increment times the base reward factor fits in 64 bits, and the sync committee is not empty.

The least inclusion delay is at most one slot.

The largest number of committees per slot is positive.

The encodings of a block body and of a state are lawful.

Then a block of the proposer passes the step of a run, with the signature and state-root checks.

It is a step of an honest continuation, and it gathers the votes of the gap. -/
theorem exists_honestBlock_gathersVotes [LawfulSszType (BeaconBlockBody preset fork)]
    [LawfulSszType (BeaconState preset fork)] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    {budget scoreBound gap : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (roots : preset.RootsReachPreviousEpoch)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (inclusion : preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤ 1)
    (committeesPositive : 0 < preset.MAX_COMMITTEES_PER_SLOT)
    {state : BeaconState preset fork} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {proposer : ValidatorIndex}
    (proposed : getBeaconProposerIndex state = .ok proposer) (honestProposer : proposer ∈ honest)
    (fresh : state.latestBlockHeader.slot < state.slot)
    (notDue : upgradeDue config ⟨fork, state⟩ = false)
    (conditions : ProposalConditions config honest key budget scoreBound gap state proposer) :
    ∃ (after : BeaconState preset fork) (engine : ExecutionEngine preset fork)
      (signed : SignedBeaconBlock preset fork) (due : upgradeDue config ⟨fork, state⟩ = false)
      (ok : applySignedBlock config .bls engine state signed true = .ok after),
      (Step.block engine signed due ok).Honest config honest key ∧
        GathersVotes honest gap state after := by
  classical
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := roots.twoSlots
    omega
  have reach := roots.reach
  have epochNat : (getCurrentEpoch state).toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
  obtain ⟨window, windowMem, windowLength⟩ := exists_window state gap positive
  -- A slot of the gap is in the epoch of the state and before it, so within one epoch of it.
  have withinEpoch : ∀ slot ∈ window,
      state.slot.toNat < slot.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    intro slot member
    obtain ⟨sameEpoch, -, -⟩ := (windowMem slot).mp member
    have slotEpochNat := congrArg UInt64.toNat sameEpoch
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at slotEpochNat
    have low := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have high := Nat.lt_mul_div_succ state.slot.toNat positive
    rw [slotEpochNat] at low
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at high
    omega
  -- A read of a root that has a value gives that value.
  obtain ⟨rootOf, rootOfOk⟩ : ∃ rootOf : Except AccessorError Root → Root,
      ∀ result root, result = .ok root → rootOf result = root :=
    ⟨fun result => match result with
      | .ok root => root
      | .error _ => default, fun _ _ read => by subst read; rfl⟩
  -- The head of each slot of the gap has a root.
  have headOk : ∀ slot ∈ window,
      getBlockRootAtSlot state slot = .ok (rootOf (getBlockRootAtSlot state slot)) := by
    intro slot member
    obtain ⟨-, before, -⟩ := (windowMem slot).mp member
    have before' := UInt64.lt_iff_toNat_lt.mp before
    have within := withinEpoch slot member
    obtain ⟨root, read⟩ := getBlockRootAtSlot_exists (state := state) (slot := slot) before'
      (by have := conditions.slotRoom; omega) (by omega) (by omega)
    rw [read, rootOfOk _ _ rfl]
  -- The first slot of the current epoch has a root, once the gap holds a slot.
  have targetOk : ∀ slot ∈ window, getBlockRoot state (getCurrentEpoch state) =
      .ok (rootOf (getBlockRoot state (getCurrentEpoch state))) := by
    intro slot member
    obtain ⟨sameEpoch, before, -⟩ := (windowMem slot).mp member
    have before' := UInt64.lt_iff_toNat_lt.mp before
    have slotEpochNat := congrArg UInt64.toNat sameEpoch
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at slotEpochNat
    have low := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have high := Nat.lt_mul_div_succ state.slot.toNat positive
    have startLe := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [slotEpochNat] at low
    obtain ⟨root, read⟩ := getBlockRoot_exists (state := state) (epoch := getCurrentEpoch state)
      (by rw [epochNat]; omega) (by rw [epochNat]; have := conditions.slotRoom; omega)
      (by rw [epochNat]; rw [Nat.mul_add, Nat.mul_one] at high; rw [Nat.mul_comm]; omega)
    rw [read, rootOfOk _ _ rfl]
  -- The data of the votes of the gap, at a slot and for a committee.
  obtain ⟨voteData, voteDataEq⟩ : ∃ voteData : Slot → CommitteeIndex → AttestationData,
      ∀ slot committeeIndex, voteData slot committeeIndex =
        { slot, index := if .pectra ≤ fork then 0 else committeeIndex,
          beaconBlockRoot := rootOf (getBlockRootAtSlot state slot),
          source := state.currentJustifiedCheckpoint,
          target :=
            ⟨getCurrentEpoch state, rootOf (getBlockRoot state (getCurrentEpoch state))⟩ } :=
    ⟨_, fun _ _ => rfl⟩
  -- An honest member of a committee of a slot of the gap casts an honest vote with that data.
  have honestVote : ∀ slot ∈ window, ∀ (committeeIndex : CommitteeIndex) members index,
      committeeIndex < getCommitteeCountPerSlot state (getCurrentEpoch state) →
      getBeaconCommittee state slot committeeIndex = .ok members → index ∈ members →
      index ∈ honest → ∀ position, (¬.pectra ≤ fork → position = committeeIndex) →
        HonestVote honest state (index, voteData slot position) := by
    intro slot member committeeIndex members index below committeeOk seated honestIndex position
      named
    obtain ⟨sameEpoch, -, -⟩ := (windowMem slot).mp member
    refine ⟨honestIndex, ?_, ?_, ?_, ?_, ?_, ⟨committeeIndex, members, below, ?_, seated, ?_⟩,
      beforeGloas⟩
    · rw [voteDataEq]
      exact sameEpoch
    · rw [voteDataEq]
      exact headOk slot member
    · rw [voteDataEq]
    · rw [voteDataEq]
    · rw [voteDataEq]
      exact targetOk slot member
    · rw [voteDataEq]
      exact committeeOk
    · rw [voteDataEq]
      by_cases electra : .pectra ≤ fork
      · simp only [electra, ↓reduceIte]
      · simp only [electra, ↓reduceIte, named electra]
  have proposerEq : ∀ block : BeaconBlock preset fork,
      HonestBlock config state (key proposer) block → block.proposerIndex = proposer :=
    fun block honestBlock => Except.ok.inj (honestBlock.proposer.symm.trans proposed)
  have registered : ∀ index ∈ insert proposer honest, ∃ validator,
      getValidator state index = .ok validator ∧
        validator.pubkey = Signatures.skToPk (key index) := by
    rw [Finset.insert_eq_of_mem honestProposer]
    exact conditions.registered
  by_cases electra : .pectra ≤ fork
  · -- From Electra the block carries one honest aggregate per slot with an honest member.
    obtain ⟨datas, datasMem, datasLength⟩ : ∃ datas : List AttestationData,
        (∀ data, data ∈ datas ↔ ∃ slot ∈ window, (∃ committeeIndex : CommitteeIndex,
          ∃ members, ∃ index,
            committeeIndex < getCommitteeCountPerSlot state (getCurrentEpoch state) ∧
            getBeaconCommittee state slot committeeIndex = .ok members ∧ index ∈ members ∧
            index ∈ honest) ∧ data = voteData slot 0) ∧ datas.length ≤ gap := by
      refine ⟨(window.filter fun slot => decide (∃ committeeIndex : CommitteeIndex,
          ∃ members, ∃ index,
            committeeIndex < getCommitteeCountPerSlot state (getCurrentEpoch state) ∧
            getBeaconCommittee state slot committeeIndex = .ok members ∧ index ∈ members ∧
            index ∈ honest)).map (voteData · 0), fun data => ?_, ?_⟩
      · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨slot, ⟨member, seated⟩, rfl⟩
          exact ⟨slot, member, seated, rfl⟩
        · rintro ⟨slot, member, seated, rfl⟩
          exact ⟨slot, ⟨member, seated⟩, rfl⟩
      · rw [List.length_map]
        exact (List.length_filter_le _ _).trans windowLength
    -- The committees of a slot of the gap with an honest member have values.
    have committeesOk : ∀ slot ∈ window, ∀ (committeeIndex : CommitteeIndex) members index,
        getBeaconCommittee state slot committeeIndex = .ok members → index ∈ members →
        ∃ committees, (List.range
            (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat).mapM
          (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees := by
      intro slot member committeeIndex members index committeeOk seated
      have sameEpoch := ((windowMem slot).mp member).1
      have room := conditions.shuffleRoom
      rw [← sameEpoch] at room ⊢
      exact committees_exists_ok committeeOk seated positive room
    -- The count of committees of a slot is at most the largest number, which is positive.
    have countBelow : (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat ≤
        preset.MAX_COMMITTEES_PER_SLOT.toNat := by
      exact toNat_getCommitteeCountPerSlot_le state _ committeesPositive
    -- Each slot of the gap with an honest member has an honest aggregate.
    obtain ⟨attestations, attestationsOk⟩ := mapM_exists_ok
        (f := honestSlotAggregate electra config state honest key) (xs := datas)
        fun data listed => by
      obtain ⟨slot, member, ⟨committeeIndex, members, index, below, committeeOk, seated,
        honestIndex⟩, rfl⟩ := (datasMem data).mp listed
      have sameEpoch := ((windowMem slot).mp member).1
      obtain ⟨committees, listedOk⟩ :=
        committeesOk slot member committeeIndex members index committeeOk seated
      refine honestSlotAggregate_exists_ok electra committeesPositive (committees := committees)
        (by rw [voteDataEq]; dsimp only; rw [sameEpoch]; exact listedOk) (fun _ => ?_)
        ⟨members, mem_of_mapM_getBeaconCommittee listedOk (UInt64.lt_iff_toNat_lt.mp below)
          committeeOk, List.ne_nil_of_mem (mem_honestSigners.mpr ⟨seated, honestIndex⟩)⟩
      -- Each committee of the slot has at most the largest size, and there are few enough.
      have sizes : ∀ size ∈ committees.map Array.size,
          size ≤ preset.MAX_VALIDATORS_PER_COMMITTEE.toNat := by
        intro size sized
        obtain ⟨committee, committeeListed, rfl⟩ := List.mem_map.mp sized
        obtain ⟨position, positionListed, read⟩ := mapM_ok_mem listedOk committee committeeListed
        exact conditions.committeeSizes slot _ committee sameEpoch
          (toUInt64_lt_of_lt (List.mem_range.mp positionListed)) read
      have total := List.sum_le_length_nsmul _ _ sizes
      rw [List.length_map, mapM_ok_length listedOk, List.length_range, smul_eq_mul] at total
      simp only [maxAttesters, electra, ↓reduceIte]
      exact total.trans (Nat.mul_comm _ _ ▸ Nat.mul_le_mul_left _ countBelow)
    have made := List.mapM_eq_ok_iff_forall₂.mp attestationsOk
    have attestationsLength : attestations.length = datas.length := mapM_ok_length attestationsOk
    have lengthFits : datas.length ≤ (parameters preset fork).MAX_ATTESTATIONS.toNat := by
      have capacity := conditions.capacity
      rw [ite_eq_left electra, Nat.mul_one] at capacity
      exact datasLength.trans capacity
    obtain ⟨engine, block, honestBlock, carried, executes, proven, registryRoom, pendingRoom,
      -⟩ := conditions.complete attestations (by rw [attestationsLength]; exact lengthFits)
    have proposerIs := proposerEq block honestBlock
    have honestBlock' : HonestBlock config state (key block.proposerIndex) block := by
      rw [proposerIs]
      exact honestBlock
    have room := conditions.room
    have scaledLe := Nat.mul_le_mul_right
      (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) lengthFits
    obtain ⟨after, processed, flagged⟩ := processBlock_honestBlock_honestSlotAggregate
      (datas := datas) electra beforeGloas apart honestBlock'
      (by rw [proposerIs]; exact registered)
      (by rw [proposerIs]; exact conditions.unslashed) fresh conditions.votesRoom periodFits proven
      registryRoom (fun before => pendingRoom electra before) conditions.scores executes
      (conditions.syncKeys _) roots conditions.slotRoom increment scaled incrementLe
      conditions.holds conditions.participation (by omega)
      (fun data listed => by
        obtain ⟨slot, -, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        exact .inr rfl)
      (fun data listed => by
        obtain ⟨slot, member, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        exact ((windowMem slot).mp member).1.symm)
      (fun data listed => by
        obtain ⟨slot, member, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        exact UInt64.lt_iff_toNat_lt.mp ((windowMem slot).mp member).2.1)
      (fun data listed => by
        obtain ⟨slot, member, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        have := UInt64.lt_iff_toNat_lt.mp ((windowMem slot).mp member).2.1
        dsimp only
        omega)
      (fun data listed => by
        obtain ⟨slot, -, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        simp)
      (fun data listed => by
        obtain ⟨slot, -, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        exact conditions.shuffleRoom)
      (fun data listed => by
        obtain ⟨slot, -, -, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq]
        simp)
      (fun data listed committees listedOk => by
        obtain ⟨slot, member, ⟨committeeIndex, members, index, below, committeeOk, seated,
          honestIndex⟩, rfl⟩ := (datasMem data).mp listed
        rw [voteDataEq] at listedOk
        obtain ⟨sameEpoch, before, within⟩ := (windowMem slot).mp member
        refine conditions.slotKeys electra slot committees sameEpoch before within listedOk ?_
        exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨members,
          mem_of_mapM_getBeaconCommittee listedOk (UInt64.lt_iff_toNat_lt.mp below) committeeOk,
          mem_honestSigners.mpr ⟨seated, honestIndex⟩⟩))
      (by rw [carried]; exact made)
    refine exists_signed_of_processBlock (by rw [proposerIs]; exact honestProposer) honestBlock'
      (registered _ (by rw [proposerIs]; exact Finset.mem_insert_self _ _)) notDue processed ?_ ?_
    · -- Each vote of the block is that of an honest member of a committee of the gap.
      rintro ⟨index, data⟩ ⟨attestation, listed, sameData, indices, indicesOk, attesting⟩
      have listed' : attestation ∈ attestations := by
        rw [← carried]
        exact Array.mem_toList_iff.mpr listed
      obtain ⟨vote, voteListed, built⟩ := exists_mem_of_forall₂ made.flip listed'
      obtain ⟨slot, member, -, rfl⟩ := (datasMem vote).mp voteListed
      obtain ⟨dataEq, signers⟩ := honestSlotAggregate_signers electra built
      obtain ⟨honestIndex, committeeIndex, committee, below, committeeOk, seated⟩ :=
        signers indices indicesOk index attesting
      dsimp only at sameData
      rw [sameData, dataEq]
      rw [voteDataEq] at below committeeOk
      dsimp only at below committeeOk
      rw [((windowMem slot).mp member).1] at below
      exact honestVote slot member committeeIndex committee index below committeeOk seated
        honestIndex 0 (fun before => absurd electra before)
    · -- Each honest member of a committee of the gap has the flag.
      intro altair' slot sameEpoch before within committeeIndex members below committeeOk member
        seated honestMember
      have windowed := (windowMem slot).mpr ⟨sameEpoch, before, within⟩
      have listed := (datasMem (voteData slot 0)).mpr
        ⟨slot, windowed, ⟨committeeIndex, members, member, below, committeeOk, seated,
          honestMember⟩, rfl⟩
      have flag := flagged _ listed (by rw [voteDataEq]; exact targetOk slot windowed)
        committeeIndex members (by rw [voteDataEq]; exact below)
        (by rw [voteDataEq]; exact committeeOk) member seated honestMember
      rw [voteDataEq] at flag
      simpa [recentParticipation] using flag
  · -- Before Electra the block carries one honest attestation per committee with an honest member.
    obtain ⟨votes, votesMem, votesLength⟩ : ∃ votes : List (AttestationData × CommitteeIndex),
        (∀ vote, vote ∈ votes ↔ ∃ slot ∈ window, ∃ committeeIndex : CommitteeIndex, ∃ members,
          committeeIndex < getCommitteeCountPerSlot state (getCurrentEpoch state) ∧
          getBeaconCommittee state slot committeeIndex = .ok members ∧
          honestSigners honest members ≠ [] ∧
          vote = (voteData slot committeeIndex, committeeIndex)) ∧
        votes.length ≤ gap * (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat := by
      refine ⟨window.flatMap fun slot => (((List.range
          (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat).map Nat.toUInt64).filter
            fun committeeIndex => decide (∃ members,
              getBeaconCommittee state slot committeeIndex = .ok members ∧
                honestSigners honest members ≠ [])).map
          fun committeeIndex => (voteData slot committeeIndex, committeeIndex),
        fun vote => ?_, ?_⟩
      · simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
          decide_eq_true_eq]
        constructor
        · rintro ⟨slot, member, committeeIndex, ⟨⟨position, below, rfl⟩, members, committeeOk,
            someSigner⟩, rfl⟩
          exact ⟨slot, member, _, members, toUInt64_lt_of_lt below, committeeOk, someSigner, rfl⟩
        · rintro ⟨slot, member, committeeIndex, members, below, committeeOk, someSigner, rfl⟩
          exact ⟨slot, member, committeeIndex, ⟨⟨committeeIndex.toNat,
            UInt64.lt_iff_toNat_lt.mp below, by simp⟩, members, committeeOk, someSigner⟩, rfl⟩
      · rw [List.length_flatMap]
        refine Nat.le_trans (List.sum_le_length_nsmul _
          (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat
          fun length listed => ?_) ?_
        · obtain ⟨slot, -, rfl⟩ := List.mem_map.mp listed
          rw [List.length_map]
          exact (List.length_filter_le _ _).trans (by simp)
        · rw [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ windowLength
    have lengthFits : votes.length ≤ (parameters preset fork).MAX_ATTESTATIONS.toNat := by
      have capacity := conditions.capacity
      rw [ite_eq_right electra] at capacity
      exact votesLength.trans capacity
    -- Each vote has an honest attestation.
    obtain ⟨attestations, attestationsOk⟩ := mapM_exists_ok
        (f := fun vote : AttestationData × CommitteeIndex =>
          honestAttestation config state honest key vote.1 vote.2) (xs := votes)
        fun vote listed => by
      obtain ⟨slot, member, committeeIndex, members, below, committeeOk, someSigner, rfl⟩ :=
        (votesMem vote).mp listed
      obtain ⟨sameEpoch, -, -⟩ := (windowMem slot).mp member
      refine honestAttestation_exists_ok (committee := members)
        (fun _ => by rw [voteDataEq]; simp [electra]) (by rw [voteDataEq]; exact committeeOk)
        (fun _ => ?_) (fun electra' => absurd electra' electra) someSigner
      simp only [maxAttesters, electra, ↓reduceIte]
      exact conditions.committeeSizes slot committeeIndex members sameEpoch below committeeOk
    have made := List.mapM_eq_ok_iff_forall₂.mp attestationsOk
    have attestationsLength : attestations.length = votes.length := mapM_ok_length attestationsOk
    obtain ⟨engine, block, honestBlock, carried, executes, proven, registryRoom, pendingRoom,
      depositRoom⟩ :=
        conditions.complete attestations (by rw [attestationsLength]; exact lengthFits)
    have proposerIs := proposerEq block honestBlock
    have honestBlock' : HonestBlock config state (key block.proposerIndex) block := by
      rw [proposerIs]
      exact honestBlock
    have room := conditions.room
    have scaledLe := Nat.mul_le_mul_right
      (state.validators.data.size * (64 * preset.baseRewardCeiling) / 448) lengthFits
    obtain ⟨after, processed, flagged⟩ := processBlock_honestBlock (votes := votes)
      altair beforeGloas apart honestBlock' (by rw [proposerIs]; exact registered)
      (by rw [proposerIs]; exact conditions.unslashed) fresh conditions.votesRoom periodFits proven
      registryRoom pendingRoom conditions.scores executes (conditions.syncKeys altair) roots
      conditions.slotRoom increment scaled incrementLe conditions.holds conditions.participation
      (by omega)
      (fun lt before => by have := depositRoom lt before; omega)
      (fun vote listed => by
        obtain ⟨slot, -, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        exact .inr rfl)
      (fun vote listed => by
        obtain ⟨slot, member, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        exact ((windowMem slot).mp member).1.symm)
      (fun vote listed => by
        obtain ⟨slot, member, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        exact UInt64.lt_iff_toNat_lt.mp ((windowMem slot).mp member).2.1)
      (fun vote listed => by
        obtain ⟨slot, member, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        have := UInt64.lt_iff_toNat_lt.mp ((windowMem slot).mp member).2.1
        dsimp only
        omega)
      (fun vote listed _ => by
        obtain ⟨slot, member, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        have := withinEpoch slot member
        dsimp only
        omega)
      (fun vote listed => by
        obtain ⟨slot, -, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq])
      (fun vote listed => by
        obtain ⟨slot, -, committeeIndex, -, below, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        exact below)
      (fun vote listed => by
        obtain ⟨slot, -, committeeIndex, -, -, -, -, rfl⟩ := (votesMem vote).mp listed
        rw [voteDataEq]
        simp)
      (fun vote listed committee committeeOk => by
        obtain ⟨slot, member, committeeIndex, members, below, membersOk, someSigner, rfl⟩ :=
          (votesMem vote).mp listed
        rw [voteDataEq] at committeeOk
        rw [membersOk, Except.ok.injEq] at committeeOk
        subst committeeOk
        obtain ⟨sameEpoch, before, within⟩ := (windowMem slot).mp member
        exact conditions.committeeKeys electra slot committeeIndex _ sameEpoch before within
          below membersOk someSigner)
      (by rw [carried]; exact made)
    refine exists_signed_of_processBlock (by rw [proposerIs]; exact honestProposer) honestBlock'
      (registered _ (by rw [proposerIs]; exact Finset.mem_insert_self _ _)) notDue processed ?_ ?_
    · -- Each vote of the block is that of an honest member of a committee of the gap.
      rintro ⟨index, data⟩ ⟨attestation, listed, sameData, indices, indicesOk, attesting⟩
      have listed' : attestation ∈ attestations := by
        rw [← carried]
        exact Array.mem_toList_iff.mpr listed
      obtain ⟨vote, voteListed, built⟩ := exists_mem_of_forall₂ made.flip listed'
      obtain ⟨slot, member, committeeIndex, members, below, -, -, rfl⟩ :=
        (votesMem vote).mp voteListed
      obtain ⟨dataEq, signers⟩ := honestAttestation_signers electra built
      obtain ⟨honestIndex, committee, committeeOk, seated⟩ :=
        signers indices indicesOk index attesting
      dsimp only at sameData
      rw [sameData, dataEq]
      rw [voteDataEq] at committeeOk
      simp only [electra, ↓reduceIte] at committeeOk
      exact honestVote slot member committeeIndex committee index below committeeOk seated
        honestIndex committeeIndex (fun _ => rfl)
    · -- Each honest member of a committee of the gap has the flag.
      intro altair' slot sameEpoch before within committeeIndex members below committeeOk member
        seated honestMember
      have windowed := (windowMem slot).mpr ⟨sameEpoch, before, within⟩
      have someSigner : honestSigners honest members ≠ [] :=
        List.ne_nil_of_mem (mem_honestSigners.mpr ⟨seated, honestMember⟩)
      have listed := (votesMem (voteData slot committeeIndex, committeeIndex)).mpr
        ⟨slot, windowed, committeeIndex, members, below, committeeOk, someSigner, rfl⟩
      have flag := flagged _ listed (by rw [voteDataEq]; exact targetOk slot windowed) members
        (by rw [voteDataEq]; exact committeeOk) member seated honestMember
      rw [voteDataEq] at flag
      simpa [recentParticipation] using flag

end EthLib.Consensus
