module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Time

/-!
# Proofs: the balance-weighted selection and the payload timeliness committee

Each validator that a balance-weighted selection draws is one of its candidates.

So each member of a payload committee sits on an attestation committee of its slot.

The indexed form of a vote lists the members whose bit is set, sorted, with any repeats.

After the window is initialized, the state reads the computed committee of each slot it covers.

The covered slots are those of the current epoch and of the lookahead.

Moving the window shifts every committee back by one epoch.

The last epoch of the moved window holds the computed committees of the epoch after the lookahead.

It computes them with one seed and one shuffle, and gives what each committee alone gives.

A payload attestation changes nothing in the state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Each validator that the search draws is a candidate, when each position of the order is.

The validators that the search starts from must be candidates too. -/
theorem mem_of_balanceWeightedSearch {indices : Array ValidatorIndex} {balances : Array Gwei}
    {order : Nat → Nat} {seed : Bytes32} {size : Nat} (nonempty : 0 < indices.size)
    (positions : ∀ place < indices.size, order place < indices.size) :
    ∀ {selected : Array ValidatorIndex} {bound : selected.size ≤ size} {i : Nat}
      {random : { random // random = drawHash fork seed i }}
      {result : Vector ValidatorIndex size}, (∀ index ∈ selected, index ∈ indices) →
      balanceWeightedSearch preset fork indices balances order seed size selected bound i random =
        .ok result →
      ∀ index ∈ result.toList, index ∈ indices := by
  -- The candidate of every draw is one of the indices.
  have candidateMem : ∀ j, indices.getD (order (j % indices.size)) 0 ∈ indices := by
    intro j
    have lt := positions _ (Nat.mod_lt j nonempty)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem lt, Option.getD_some]
    exact Array.getElem_mem lt
  intro selected bound i random result start found
  -- Each step either returns or moves closer to the end of the counter.
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing selected i random with
  | _ left ih =>
    unfold balanceWeightedSearch at found
    split at found
    · cases found
      intro index member
      exact start index (by simpa using member)
    simp only [bind, Except.bind] at found
    split at found
    · cases found
    rename_i accepted _
    split at found
    · refine ih (2 ^ 64 - (i + 1)) (by omega) ?_ found rfl
      split
      · intro index member
        rcases Array.mem_push.mp member with old | new
        · exact start index old
        · exact new ▸ candidateMem i
      · exact start
    · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found

/-- Two orders that agree on the positions below the number of candidates give one search.

The search reads the order only at a draw number modulo that number. -/
theorem balanceWeightedSearch_congr {indices : Array ValidatorIndex} {balances : Array Gwei}
    {first second : Nat → Nat} {seed : Bytes32} {size : Nat} (nonempty : 0 < indices.size)
    (agree : ∀ place < indices.size, first place = second place) :
    ∀ {selected : Array ValidatorIndex} {bound : selected.size ≤ size} {i : Nat}
      {random : { random // random = drawHash fork seed i }},
      balanceWeightedSearch preset fork indices balances first seed size selected bound i random =
        balanceWeightedSearch preset fork indices balances second seed size selected bound i
          random := by
  intro selected bound i random
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing selected i random with
  | _ left ih =>
    unfold balanceWeightedSearch
    split
    · rfl
    simp only [agree _ (Nat.mod_lt i nonempty), bind, Except.bind]
    split
    · rfl
    split
    · exact ih _ (by omega) rfl
    · rfl

/-- Each validator that a balance-weighted selection draws is one of its candidates. -/
theorem mem_of_computeBalanceWeightedSelection {state : BeaconState preset fork}
    {indices : Array ValidatorIndex} {seed : Bytes32} {size : UInt64} {shuffleIndices : Bool}
    {result : Vector ValidatorIndex size.toNat}
    (computed :
      computeBalanceWeightedSelection state indices seed size shuffleIndices = .ok result) :
    ∀ index ∈ result.toList, index ∈ indices := by
  unfold computeBalanceWeightedSelection at computed
  by_cases empty : indices.size = 0
  · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed
  by_cases fits : indices.size < 2 ^ 64
  · simp only [empty, fits, ↓reduceIte, bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    split at computed
    · cases computed
    refine mem_of_balanceWeightedSearch (Nat.pos_of_ne_zero empty) ?_ (by simp) computed
    intro place lt
    split
    · exact Shuffle.shuffledIndex_lt lt
    · exact lt
  · simp [empty, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed

/-- A slot has at least one attestation committee. -/
theorem getCommitteeCountPerSlot_pos (state : BeaconState preset fork) (epoch : Epoch) :
    0 < (getCommitteeCountPerSlot state epoch).toNat := by
  have atLeastOne : ∀ x : UInt64, 0 < (max 1 x).toNat := by
    intro x
    simp only [max]
    split
    · rename_i le
      rw [UInt64.le_iff_toNat_le] at le
      simp only [UInt64.toNat_one] at le
      exact le
    · simp
  exact atLeastOne _

/-- The members of the committees of a slot are those of each committee, one after the other.

The committees of the slot share one shuffle, and each committee alone gives the same members. -/
theorem slotCommitteeMembers_eq (state : BeaconState preset fork) (slot : Slot) :
    slotCommitteeMembers state slot =
      (List.range (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).foldlM
        (fun members index => return members ++ (← getBeaconCommittee state slot index.toUInt64))
        #[] := by
  unfold slotCommitteeMembers attesterShuffle slotCommitteeMembersOf
  -- The first committee reads the same seed and shuffle, so a failure of either is on both sides.
  obtain ⟨n, count⟩ : ∃ n,
      (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (getCommitteeCountPerSlot_pos _ _)).symm⟩
  cases seedOk : getSeed state (computeEpochAtSlot preset slot) DOMAIN_BEACON_ATTESTER with
  | error e =>
    rw [count, List.range_succ_eq_map, List.foldlM_cons]
    simp [getBeaconCommittee, seedOk, bind, Except.bind]
  | ok seed =>
    cases shuffleOk : computeShuffledPermutation preset
        (UInt64.ofNat (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length)
        seed with
    | error e =>
      rw [count, List.range_succ_eq_map, List.foldlM_cons]
      simp [getBeaconCommittee, seedOk, shuffleOk, bind, Except.bind, Except.mapError]
    | ok shuffled =>
      simp only [seedOk, List.size_toArray, shuffleOk, Except.mapError, bind, Except.bind, pure,
        Except.pure]
      congr 1
      funext members index
      simp [getBeaconCommittee, seedOk, shuffleOk, bind, Except.bind, Except.mapError]

/-- Each member of the payload committee of a slot is on an attestation committee of the slot. -/
theorem mem_of_computePtc {state : BeaconState preset fork} {slot : Slot}
    {committee : PayloadTimelinessCommittee preset}
    (computed : computePtc state slot = .ok committee) :
    ∃ members, slotCommitteeMembers state slot = .ok members ∧
      ∀ index ∈ committee.toList, index ∈ members := by
  simp only [computePtc, computePtcOf, bind_ok_iff] at computed
  obtain ⟨_, _, ⟨active, shuffled⟩, shuffleOk, members, found, selected⟩ := computed
  refine ⟨members, ?_, mem_of_computeBalanceWeightedSelection selected⟩
  simp only [slotCommitteeMembers, shuffleOk, bind, Except.bind]
  exact found

/-- Each attester of a committee is a member of it. -/
theorem mem_of_ptcAttesters {committee : PayloadTimelinessCommittee preset}
    {bits : PayloadTimelinessCommitteeBits preset} {index : ValidatorIndex}
    (member : index ∈ ptcAttesters committee bits) : index ∈ committee.toList := by
  simp only [ptcAttesters, List.mem_filterMap] at member
  obtain ⟨⟨candidate, bit⟩, pair, chosen⟩ := member
  split at chosen
  · cases chosen
    exact (List.of_mem_zip pair).1
  · cases chosen

/-- The indexed form of a vote lists the members of its committee whose bit is set, sorted.

It keeps the vote and the signature. -/
theorem getIndexedPayloadAttestation_spec {config : Config} {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {attestation : PayloadAttestation preset}
    {indexed : IndexedPayloadAttestation preset}
    (computed : getIndexedPayloadAttestation config state gloas attestation = .ok indexed) :
    ∃ committee, getPtc config state gloas attestation.data.slot = .ok committee ∧
      indexed.attestingIndices.data.toList =
        (ptcAttesters committee attestation.aggregationBits).mergeSort (· ≤ ·) ∧
      indexed.data = attestation.data ∧ indexed.signature = attestation.signature := by
  simp only [getIndexedPayloadAttestation, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨committee, found, rfl⟩ := computed
  exact ⟨committee, found, by simp, rfl, rfl⟩

/-- The indices of the indexed form of a vote never decrease, and each is in the committee. -/
theorem getIndexedPayloadAttestation_sorted {config : Config} {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {attestation : PayloadAttestation preset}
    {indexed : IndexedPayloadAttestation preset}
    (computed : getIndexedPayloadAttestation config state gloas attestation = .ok indexed) :
    ∃ committee, getPtc config state gloas attestation.data.slot = .ok committee ∧
      indexed.attestingIndices.data.toList.Pairwise (· ≤ ·) ∧
      ∀ index ∈ indexed.attestingIndices.data.toList, index ∈ committee.toList := by
  obtain ⟨committee, found, indices, _, _⟩ := getIndexedPayloadAttestation_spec computed
  refine ⟨committee, found, indices ▸ mergeSort_sorted _, fun index member => ?_⟩
  rw [indices, List.mem_mergeSort] at member
  exact mem_of_ptcAttesters member

/-- A payload attestation changes nothing in the state. -/
theorem processPayloadAttestation_eq {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {attestation : PayloadAttestation preset}
    (computed : processPayloadAttestation config checks state gloas attestation = .ok after) :
    after = state := by
  simp only [processPayloadAttestation, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, same⟩ := computed
  exact same.symm

/-- A position of the window within its first epoch names a slot of that epoch. -/
theorem computeEpochAtSlot_ptcWindowSlot {epoch : Epoch} {position : Nat} {slot : Slot}
    (first : position < preset.SLOTS_PER_EPOCH.toNat)
    (computed : ptcWindowSlot preset epoch position = .ok slot) :
    computeEpochAtSlot preset slot = epoch := by
  simp only [ptcWindowSlot, liftArith, mapError_ok_iff, bind_ok_iff, addChecked_ok_iff,
    computeStartSlotAtEpoch, mulChecked_ok_iff] at computed
  obtain ⟨same, ⟨_, sameNat⟩, start, ⟨_, startNat⟩, _, slotNat⟩ := computed
  have smallPosition : position < 2 ^ 64 :=
    Nat.lt_trans first preset.SLOTS_PER_EPOCH.toNat_lt
  rw [Nat.div_eq_of_lt first, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.zero_mod,
    Nat.add_zero] at sameNat
  rw [Nat.mod_eq_of_lt first, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt smallPosition] at slotNat
  apply UInt64.toNat_inj.mp
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) first
  rw [computeEpochAtSlot, UInt64.toNat_div, slotNat, startNat, sameNat, Nat.add_comm,
    Nat.add_mul_div_right _ _ positive, Nat.div_eq_of_lt first, Nat.zero_add]

/-- Moving the window computes each new committee as the committee of its slot.

The new committees share the two seeds and the shuffle of their epoch, with the same result.

The two sides fail with the same error too. -/
theorem processPtcWindow_eq (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    processPtcWindow state gloas = (do
      let window := (state.ptcWindow gloas).elements
      let perEpoch := preset.SLOTS_PER_EPOCH.toNat
      let nextEpoch ← liftArith do
        addChecked (← addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD) 1
      let moved ← (Vector.range _).mapM fun position =>
        if kept : position + perEpoch < _ then pure window[position + perEpoch]
        else do
          computePtc state (← ptcWindowSlot preset nextEpoch (position + perEpoch - window.size))
      return { state with ptcWindow := fun _ => .ofVector moved }) := by
  unfold processPtcWindow
  simp only [bind, Except.bind]
  split
  · rfl
  rename_i nextEpoch _
  rw [vector_mapM_congr (g := fun position =>
      if kept : position + preset.SLOTS_PER_EPOCH.toNat < _ then
        pure (state.ptcWindow gloas).elements[position + preset.SLOTS_PER_EPOCH.toNat]
      else do
        computePtc state (← ptcWindowSlot preset nextEpoch
          (position + preset.SLOTS_PER_EPOCH.toNat - (state.ptcWindow gloas).elements.size)))]
  · rfl
  intro position inRange
  simp only [Vector.getElem_range]
  split
  · rfl
  rename_i last
  simp only [bind, Except.bind]
  split
  · rfl
  rename_i slot computed
  -- The slot is in the new epoch, so its committee reads the seeds and shuffle of that epoch.
  have size : (state.ptcWindow gloas).elements.size =
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat := rfl
  have epoch := computeEpochAtSlot_ptcWindowSlot (by omega) computed
  cases seedOk : getSeed state nextEpoch DOMAIN_PTC_ATTESTER <;>
    cases shuffleOk : attesterShuffle state nextEpoch <;>
    simp [computePtc, epoch, seedOk, shuffleOk, bind, Except.bind, pure, Except.pure]

/-- After the window is initialized, the state reads the computed committee of each slot it covers.

The covered slots are those of the current epoch and of the lookahead.

Moving the window shifts every committee back by one epoch.

The last epoch holds the computed committees of the epoch after the lookahead. -/
theorem processPtcWindow_spec {state after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} (computed : processPtcWindow state gloas = .ok after) :
    (∀ (position : Nat) (kept : position + preset.SLOTS_PER_EPOCH.toNat <
        (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat),
      (after.ptcWindow gloas)[position] =
        (state.ptcWindow gloas)[position + preset.SLOTS_PER_EPOCH.toNat]) ∧
    ∃ nextEpoch : Epoch,
      nextEpoch.toNat = (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 ∧
      ∀ (position : Nat) (inRange : position <
          (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat),
        (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat ≤
          position + preset.SLOTS_PER_EPOCH.toNat →
        ∃ slot, ptcWindowSlot preset nextEpoch (position + preset.SLOTS_PER_EPOCH.toNat -
            (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat) = .ok slot ∧
          computePtc state slot = .ok (after.ptcWindow gloas)[position] := by
  rw [processPtcWindow_eq] at computed
  simp only [bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨lookahead, ⟨_, first⟩, _, second⟩, moved, movedOk, rfl⟩ := computed
  have one : (1 : UInt64).toNat = 1 := rfl
  refine ⟨fun position kept => ?_, nextEpoch, by omega, fun position inRange last => ?_⟩
  · have entry := vector_mapM_ok_getElem movedOk position (by omega)
    simp only [Vector.getElem_range, kept, ↓reduceDIte, Except.ok.injEq] at entry
    exact entry.symm
  · have entry := vector_mapM_ok_getElem movedOk position inRange
    simp only [Vector.getElem_range] at entry
    split at entry
    · omega
    simp only [bind_ok_iff] at entry
    obtain ⟨slot, slotOk, ptc⟩ := entry
    exact ⟨slot, slotOk, ptc⟩

/-- The position in the window of a slot of the current epoch or of the lookahead.

It is one epoch of slots for the previous epoch, then the epochs up to that of the slot.

The window must fit in 64 bits, and so must the last epoch of the lookahead. -/
theorem ptcWindowPosition_of_le {config : Config} {state : BeaconState preset fork}
    {slot : Slot} (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (forkEpoch : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset slot)
    (current : getCurrentEpoch state ≤ computeEpochAtSlot preset slot)
    (lookahead : (computeEpochAtSlot preset slot).toNat ≤
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat)
    (fits : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < 2 ^ 64)
    (windowFits :
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ position, ptcWindowPosition config state slot = .ok position ∧
      position.toNat = ((computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat
        + 1) * preset.SLOTS_PER_EPOCH.toNat + slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
  have currentNat := UInt64.le_iff_toNat_le.mp current
  have remainder : (slot % preset.SLOTS_PER_EPOCH).toNat < preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ positive
  have last : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD).toNat =
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat :=
    toNat_add_of_lt fits
  have difference : (computeEpochAtSlot preset slot - getCurrentEpoch state).toNat =
      (computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat :=
    UInt64.toNat_sub_of_le _ _ current
  have spread : ((computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat ≤
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have mulFits : ((computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by omega
  have oneFits : (computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat + 1 <
      2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ positive) mulFits
  have oneOk :
      (computeEpochAtSlot preset slot - getCurrentEpoch state).toNat + (1 : UInt64).toNat <
        2 ^ 64 := by
    rw [difference, show (1 : UInt64).toNat = 1 from rfl]
    exact oneFits
  obtain ⟨plusOne, plusOneOk⟩ : ∃ value, addChecked
      (computeEpochAtSlot preset slot - getCurrentEpoch state) 1 = .ok value :=
    ⟨_, by simp only [addChecked, oneOk, ↓reduceIte]; rfl⟩
  have plusOneNat := (addChecked_ok_iff.mp plusOneOk).2
  rw [difference, show (1 : UInt64).toNat = 1 from rfl] at plusOneNat
  have offsetFits : plusOne.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    rw [plusOneNat]
    exact mulFits
  obtain ⟨offset, offsetOk⟩ : ∃ value, mulChecked plusOne preset.SLOTS_PER_EPOCH = .ok value :=
    ⟨_, by simp only [mulChecked, offsetFits, ↓reduceIte]; rfl⟩
  have offsetNat := (mulChecked_ok_iff.mp offsetOk).2
  rw [plusOneNat] at offsetNat
  have positionFits : offset.toNat + (slot % preset.SLOTS_PER_EPOCH).toNat < 2 ^ 64 := by
    rw [offsetNat]
    omega
  obtain ⟨position, positionOk⟩ : ∃ value,
      addChecked offset (slot % preset.SLOTS_PER_EPOCH) = .ok value :=
    ⟨_, by simp only [addChecked, positionFits, ↓reduceIte]; rfl⟩
  have positionNat := (addChecked_ok_iff.mp positionOk).2
  rw [offsetNat, UInt64.toNat_mod] at positionNat
  refine ⟨position, ?_, positionNat⟩
  have notBefore : ¬computeEpochAtSlot preset slot < getCurrentEpoch state :=
    fun before => absurd (UInt64.lt_iff_toNat_lt.mp before) (by omega)
  have within : computeEpochAtSlot preset slot ≤
      getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD := by
    rw [UInt64.le_iff_toNat_le, last]
    exact lookahead
  have lastOk : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD =
      .ok (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD) :=
    addChecked_ok_iff.mpr ⟨fits, last⟩
  simp [ptcWindowPosition, forkEpoch, notBefore, liftArith, lastOk, within, plusOneOk,
    offsetOk, positionOk, bind, Except.bind, Except.mapError]

/-- After the window is initialized, the state reads the computed committee of a slot.

The slot must be from the fork, in the current epoch or the lookahead.

The window must fit in 64 bits, and so must the last epoch of the lookahead. -/
theorem getPtc_initializePtcWindow {config : Config} {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {window : PayloadTimelinessCommitteeWindow preset}
    (initialized : initializePtcWindow state = .ok window) {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (forkEpoch : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset slot)
    (current : getCurrentEpoch state ≤ computeEpochAtSlot preset slot)
    (lookahead : (computeEpochAtSlot preset slot).toNat ≤
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat)
    (fits : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < 2 ^ 64)
    (windowFits :
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    getPtc config { state with ptcWindow := fun _ => window } gloas slot =
      computePtc state slot := by
  -- The window is the vector of computed committees, with its tree.
  unfold initializePtcWindow at initialized
  obtain ⟨committees, mapped, rfl⟩ := map_ok_iff.mp initialized
  obtain ⟨position, positionOk, positionNat⟩ :=
    ptcWindowPosition_of_le (state := state) positive forkEpoch current lookahead fits windowFits
  -- The names of the epochs and of the slot as natural numbers.
  have epochNat : (computeEpochAtSlot preset slot).toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat := UInt64.toNat_div _ _
  have currentNat := UInt64.le_iff_toNat_le.mp current
  have spread : ((computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat ≤
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have remainder := Nat.mod_lt slot.toNat positive
  have inRange : position.toNat <
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat := by omega
  -- The entry of the window at that position is the computed committee of some slot.
  have entry := vector_mapM_ok_getElem mapped position.toNat inRange
  simp only [Vector.getElem_range] at entry
  split at entry
  · rw [positionNat] at *
    rename_i before
    exact absurd before (by rw [Nat.succ_mul] at *; omega)
  simp only [bind_ok_iff] at entry
  obtain ⟨other, otherOk, computed⟩ := entry
  -- That slot is the slot itself.
  have offsetNat : position.toNat - preset.SLOTS_PER_EPOCH.toNat =
      ((computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat + slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
    rw [positionNat, Nat.succ_mul]
    omega
  have quotient : (position.toNat - preset.SLOTS_PER_EPOCH.toNat) /
      preset.SLOTS_PER_EPOCH.toNat =
      (computeEpochAtSlot preset slot).toNat - (getCurrentEpoch state).toNat := by
    rw [offsetNat, Nat.add_comm, Nat.add_mul_div_right _ _ positive,
      Nat.div_eq_of_lt remainder, Nat.zero_add]
  have rest : (position.toNat - preset.SLOTS_PER_EPOCH.toNat) %
      preset.SLOTS_PER_EPOCH.toNat = slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
    rw [offsetNat, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  simp only [ptcWindowSlot, liftArith, mapError_ok_iff, bind_ok_iff, addChecked_ok_iff,
    computeStartSlotAtEpoch, mulChecked_ok_iff] at otherOk
  obtain ⟨epoch, ⟨_, epochSum⟩, start, ⟨_, startNat⟩, _, otherNat⟩ := otherOk
  have small : (position.toNat - preset.SLOTS_PER_EPOCH.toNat) %
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ positive) (by
    have := preset.SLOTS_PER_EPOCH.toNat_lt
    omega)
  have smallQuotient : (position.toNat - preset.SLOTS_PER_EPOCH.toNat) /
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    rw [quotient]
    have := (computeEpochAtSlot preset slot).toNat_lt
    omega
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt smallQuotient, quotient] at epochSum
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small, rest] at otherNat
  have same : other = slot := by
    apply UInt64.toNat_inj.mp
    rw [otherNat, startNat, epochSum, Nat.add_sub_cancel' currentNat, epochNat]
    exact Nat.div_add_mod' _ _
  subst same
  rw [computed]
  have moved : ptcWindowPosition config
      { state with ptcWindow := fun _ => .ofVector committees } other =
      .ok position := positionOk
  have read : (RootedVector.ofVector committees).elements = committees := rfl
  simp [getPtc, moved, read, bind, Except.bind, pure, Except.pure, inRange]

end EthLib.Consensus
