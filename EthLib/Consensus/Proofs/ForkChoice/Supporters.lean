module

public import EthLib.Consensus.Proofs.ForkChoice.AttestationScores
public import EthLib.Consensus.Proofs.Transition.FfgStake

/-!
# Proofs: the supporters of a node and their stake

The supporters of a node are the validators that count in a state and whose vote counts for it.

They are active and not slashed in that state.

Their stake, by effective balance, is the store's votes for the node, at every fork.

That needs the registry of the state within the limit of the preset, so that indices stay apart.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models

variable {preset : Preset} {fork : Fork}

/-- An index is in the unslashed active list when it names a validator active and not slashed.

The registry must stay within the limit of the preset, so that indices keep their value. -/
theorem mem_unslashedActiveBalances_iff {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {v : ValidatorIndex} :
    v ∈ (unslashedActiveBalances state).map (·.1) ↔
      ∃ validator, state.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch state) = true ∧ validator.slashed = false := by
  simp only [List.mem_map, unslashedActiveBalances, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.exists]
  constructor
  · rintro ⟨_, _, ⟨validator, position, inZip, flags, same⟩, rfl⟩
    cases same
    have found := List.mem_zipIdx_iff_getElem?.mp inZip
    have lt : position < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at flags
    refine ⟨validator, ?_, flags.1, flags.2⟩
    rw [toNat_toUInt64_of_lt within lt]
    simpa using found
  · rintro ⟨validator, found, active, slashed⟩
    refine ⟨v, validator.effectiveBalance, ⟨validator, v.toNat,
      List.mem_zipIdx_iff_getElem?.mpr (by simpa using found), by simp [active, slashed], ?_⟩, rfl⟩
    simp

namespace Store

variable (store : Store preset fork)

/-- The validators whose votes the store counts for a node, from a state.

They are active and not slashed in that state, and their latest vote counts for the node. -/
def supportersOf (state : BeaconState preset fork) (node : ForkChoiceNode) :
    Finset ValidatorIndex :=
  (((unslashedActiveBalances state).filter (store.voteCountsFor node ·.1)).map (·.1)).toFinset

variable {store}

/-- The votes that the store counts for a node are the stake of its supporters.

A validator weighs its effective balance in the state.

The registry of the state must stay within the limit of the preset. -/
theorem stake_supportersOf {node : ForkChoiceNode} {state : BeaconState preset fork}
    {score : Gwei} (within : state.RegistryWithinLimit)
    (computed : store.getAttestationScore node state = .ok score) :
    stake (fun v => balanceAt state v.toNat) (store.supportersOf state node) = score.toNat := by
  set entries := unslashedActiveBalances state
  -- Each entry is a position of the registry with its effective balance.
  have balance : ∀ entry ∈ entries, balanceAt state entry.1.toNat = entry.2.toNat := by
    rintro ⟨index, gwei⟩ member
    simp only [entries, unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at member
    obtain ⟨validator, i, inZip, -, rfl, rfl⟩ := member
    have found := (List.mem_zipIdx_iff_getElem?.mp inZip)
    have lt : i < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    rw [toNat_toUInt64_of_lt within lt]
    simp [balanceAt, by simpa using found]
  -- The positions are distinct.
  have distinct : (entries.map (·.1)).Nodup := by
    have sorted := validatorPositions_sorted within
      fun validator => isActiveValidator validator (getCurrentEpoch state) && !validator.slashed
    have same : entries.map (·.1) = state.validators.data.toList.zipIdx.filterMap
        fun (validator, index) =>
          if isActiveValidator validator (getCurrentEpoch state) && !validator.slashed then
            some index.toUInt64
          else none := by
      simp only [entries, unslashedActiveBalances, List.map_filterMap]
      congr 1
      funext entry
      split <;> rfl
    rw [same]
    exact sorted.imp UInt64.ne_of_lt
  have chosen := ((List.filter_sublist (p := fun entry : ValidatorIndex × Gwei =>
    store.voteCountsFor node entry.1) (l := entries)).map (·.1)).nodup distinct
  rw [supportersOf, stake, List.sum_toFinset _ chosen, List.map_map,
    store.getAttestationScore_toNat_eq_sum computed]
  exact (congrArg List.sum (List.map_congr_left (g := fun entry => entry.2.toNat)
    fun entry member => balance entry (List.mem_of_mem_filter member))).trans
      (by simpa using (EthLib.Base.sum_map_ite_eq_sum_filter
        (fun entry => store.voteCountsFor node entry.1 = true) _ entries).symm)

/-- The vote of each supporter of a node counts for that node. -/
theorem voteCountsFor_of_mem_supportersOf {state : BeaconState preset fork}
    {node : ForkChoiceNode} {v : ValidatorIndex} (member : v ∈ store.supportersOf state node) :
    store.voteCountsFor node v = true := by
  simp only [supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at member
  obtain ⟨⟨index, gwei⟩, ⟨-, counts⟩, rfl⟩ := member
  exact counts

/-- A supporter is active in the state that it counts in.

The registry of the state must stay within the limit of the preset. -/
theorem isActiveAt_of_mem_supportersOf {state : BeaconState preset fork} {node : ForkChoiceNode}
    {v : ValidatorIndex} (within : state.RegistryWithinLimit)
    (member : v ∈ store.supportersOf state node) :
    isActiveAt state (getCurrentEpoch state) v.toNat = true := by
  simp only [supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at member
  obtain ⟨⟨index, gwei⟩, ⟨inside, -⟩, rfl⟩ := member
  obtain ⟨validator, found, active, -⟩ :=
    (mem_unslashedActiveBalances_iff within).mp (List.mem_map.mpr ⟨_, inside, rfl⟩)
  simp [isActiveAt, found, active]

end Store

end EthLib.Consensus
