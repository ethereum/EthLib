module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.Supporters

/-!
# Proofs: a static set of validators, Assumption 1 of the fast confirmation paper

Assumption 1 of [arXiv 2405.00549v4][fcr], in §3.2, keeps the validators and their weights fixed.

The only change it allows is the slashing of Byzantine validators.

The head weighs votes with the state of the justified checkpoint of the store.

The fast confirmation rule weighs them with a state of an observed justified checkpoint.

Under the assumption the proof can compare the two weights through one reference state.

Here the assumption is a relation between the reference state and each state that a store holds.

It keeps only what the proofs use, and takes the validator set of the paper as the active one.

Each honest validator is active and not slashed in both states, with the same effective balance.

No effective balance is above that of the reference.

A Byzantine validator active and not slashed in the state is so in the reference too.

Then the honest supporters of a node weigh the same in two such states.

The supporters of a node in a state weigh at most its supporters in the reference.

A store built from an anchor holds only the anchor state, which agrees with itself.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models

variable {preset : Preset} {fork : Fork}

/-- A state agrees with a reference state on a static set of validators, with `J` the honest ones.

No effective balance is above that of the reference.

Each honest validator is active and not slashed in both states, with one effective balance.

A Byzantine validator active and not slashed in the state is so in the reference too. -/
structure StaticPair (J : Set ValidatorIndex) (ref state : BeaconState preset fork) : Prop where
  /-- No effective balance is above that of the reference. -/
  balance_le : ∀ i, balanceAt state i ≤ balanceAt ref i
  /-- Each honest validator is active and not slashed in both states, with one effective balance. -/
  honest : ∀ v ∈ J, ∃ validator validator',
    state.validators.data[v.toNat]? = some validator ∧
    ref.validators.data[v.toNat]? = some validator' ∧
    validator.slashed = false ∧ validator'.slashed = false ∧
    isActiveValidator validator (getCurrentEpoch state) = true ∧
    isActiveValidator validator' (getCurrentEpoch ref) = true ∧
    validator.effectiveBalance = validator'.effectiveBalance
  /-- A Byzantine validator active and not slashed in the state is so in the reference too. -/
  byzantine : ∀ v : ValidatorIndex, v ∉ J → ∀ validator,
    state.validators.data[v.toNat]? = some validator → validator.slashed = false →
    isActiveValidator validator (getCurrentEpoch state) = true →
    ∃ validator', ref.validators.data[v.toNat]? = some validator' ∧
      validator'.slashed = false ∧ isActiveValidator validator' (getCurrentEpoch ref) = true

/-- Every state that a store holds, for a block or a checkpoint, agrees with the reference. -/
def StaticStore (J : Set ValidatorIndex) (ref : BeaconState preset fork)
    (store : Store preset fork) : Prop :=
  (∀ (root : Root) state, store.blockStates[root]? = some state → StaticPair J ref state) ∧
    ∀ (checkpoint : Checkpoint) state, store.checkpointStates[checkpoint]? = some state →
      StaticPair J ref state

variable {J : Set ValidatorIndex} {ref state : BeaconState preset fork}

/-- A state agrees with itself when each honest validator is active and not slashed in it. -/
theorem staticPair_self
    (honest : ∀ v ∈ J, ∃ validator, state.validators.data[v.toNat]? = some validator ∧
      validator.slashed = false ∧ isActiveValidator validator (getCurrentEpoch state) = true) :
    StaticPair J state state := by
  refine ⟨fun _ => le_rfl, fun v hv => ?_, fun v _ validator found slashed active => ?_⟩
  · obtain ⟨validator, found, slashed, active⟩ := honest v hv
    exact ⟨validator, validator, found, found, slashed, slashed, active, active, rfl⟩
  · exact ⟨validator, found, slashed, active⟩

/-- Honest validators weigh the same in a state that agrees with the reference. -/
theorem stake_eq_of_staticPair (static : StaticPair J ref state) (S : Finset ValidatorIndex)
    (honest : ∀ v ∈ S, v ∈ J) :
    stake (fun v => balanceAt state v.toNat) S = stake (fun v => balanceAt ref v.toNat) S := by
  refine stake_congr fun v hv => ?_
  obtain ⟨validator, validator', found, found', -, -, -, -, eq⟩ := static.honest v (honest v hv)
  simp [balanceAt, found, found', eq]

/-- A store built from an anchor agrees with the anchor state as reference.

Each honest validator must be active and not slashed in the anchor state. -/
theorem staticStore_getForkchoiceStore {config : Config} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (made : getForkchoiceStore config state anchorBlock = .ok store)
    (honest : ∀ v ∈ J, ∃ validator, state.validators.data[v.toNat]? = some validator ∧
      validator.slashed = false ∧ isActiveValidator validator (getCurrentEpoch state) = true) :
    StaticStore J state store := by
  obtain ⟨r, -, -, states⟩ := getForkchoiceStore_maps made
  obtain ⟨r', -, cps⟩ := getForkchoiceStore_checkpointStates made
  have self := staticPair_self (state := state) honest
  refine ⟨fun root found_state found => ?_, fun cp found_state found => ?_⟩
  · rw [states, Std.TreeMap.getElem?_insert] at found
    split at found
    · cases found
      exact self
    · simp at found
  · rw [cps, Std.TreeMap.getElem?_insert] at found
    split at found
    · cases found
      exact self
    · simp at found

namespace Store

variable {store : Store preset fork} {first second : BeaconState preset fork}

/-- A supporter is a validator of the registry that is active, not slashed and counted. -/
private theorem mem_supportersOf_iff {state : BeaconState preset fork} {node : ForkChoiceNode}
    {v : ValidatorIndex} (within : state.RegistryWithinLimit) :
    v ∈ store.supportersOf state node ↔
      ∃ validator, state.validators.data[v.toNat]? = some validator ∧
      isActiveValidator validator (getCurrentEpoch state) = true ∧ validator.slashed = false ∧
      store.voteCountsFor node v = true := by
  constructor
  · intro member
    have counts := voteCountsFor_of_mem_supportersOf member
    simp only [supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at member
    obtain ⟨⟨index, gwei⟩, ⟨inside, -⟩, rfl⟩ := member
    simp only [unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at inside
    obtain ⟨validator, i, inZip, isActive, rfl, -⟩ := inside
    have found := List.mem_zipIdx_iff_getElem?.mp inZip
    have lt : i < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at isActive
    refine ⟨validator, ?_, isActive.1, isActive.2, counts⟩
    rw [toNat_toUInt64_of_lt within lt]
    simpa using found
  · rintro ⟨validator, found, active, slashed, counts⟩
    have lt : v.toNat < state.validators.data.size := by
      exact (Array.getElem?_eq_some_iff.mp found).1
    simp only [supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
    refine ⟨(v, validator.effectiveBalance), ⟨?_, counts⟩, rfl⟩
    simp only [unslashedActiveBalances, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Prod.mk.injEq, Prod.exists]
    refine ⟨validator, v.toNat, List.mem_zipIdx_iff_getElem?.mpr (by simpa using found),
      by simp [active, slashed], ?_, rfl⟩
    simp

/-- The honest supporters of a node weigh the same in two states that agree with one reference.

The registries of both states must stay within the limit of the preset. -/
theorem stake_honest_supportersOf_eq_of_staticPair [DecidablePred (· ∈ J)]
    (withinFirst : first.RegistryWithinLimit) (withinSecond : second.RegistryWithinLimit)
    (staticFirst : StaticPair J ref first) (staticSecond : StaticPair J ref second)
    (node : ForkChoiceNode) :
    stake (fun v => balanceAt first v.toNat) {v ∈ store.supportersOf first node | v ∈ J} =
      stake (fun v => balanceAt second v.toNat) {v ∈ store.supportersOf second node | v ∈ J} := by
  have same : {v ∈ store.supportersOf first node | v ∈ J} =
      {v ∈ store.supportersOf second node | v ∈ J} := by
    ext v
    simp only [Finset.mem_filter, and_congr_left_iff]
    intro hv
    obtain ⟨a, b, fa, fb, sa, sb, aa, ab, -⟩ := staticFirst.honest v hv
    obtain ⟨c, d, fc, fd, sc, sd, ac, ad, -⟩ := staticSecond.honest v hv
    rw [mem_supportersOf_iff withinFirst, mem_supportersOf_iff withinSecond]
    simp only [fa, fc, Option.some.injEq, exists_eq_left', sa, aa, sc, ac]
  rw [same]
  exact (stake_eq_of_staticPair staticFirst _ fun v hv => (Finset.mem_filter.mp hv).2).trans
    (stake_eq_of_staticPair staticSecond _ fun v hv => (Finset.mem_filter.mp hv).2).symm

/-- The supporters of a node in a state weigh at most its supporters in the reference.

The registries of both states must stay within the limit of the preset. -/
theorem stake_supportersOf_le_of_staticPair (within : state.RegistryWithinLimit)
    (withinRef : ref.RegistryWithinLimit) (static : StaticPair J ref state)
    (node : ForkChoiceNode) :
    stake (fun v => balanceAt state v.toNat) (store.supportersOf state node) ≤
      stake (fun v => balanceAt ref v.toNat) (store.supportersOf ref node) := by
  have subset : store.supportersOf state node ⊆ store.supportersOf ref node := by
    intro v member
    obtain ⟨validator, found, active, slashed, counts⟩ :=
      (mem_supportersOf_iff within).mp member
    by_cases hv : v ∈ J
    · obtain ⟨a, b, fa, fb, sa, sb, aa, ab, -⟩ := static.honest v hv
      rw [mem_supportersOf_iff withinRef]
      exact ⟨b, fb, ab, sb, counts⟩
    · obtain ⟨b, fb, sb, ab⟩ := static.byzantine v hv validator found slashed active
      rw [mem_supportersOf_iff withinRef]
      exact ⟨b, fb, ab, sb, counts⟩
  exact (show stake _ _ ≤ stake _ _ from
    Finset.sum_le_sum fun v _ => static.balance_le v.toNat).trans
    (stake_mono (w := fun v => balanceAt ref v.toNat) subset)

end Store

namespace Models.Network

/-- An execution keeps a static set of validators.

At all times, each state that the store of an honest validator holds agrees with the reference.

This is the part of Assumption 1 of the paper that the proofs use, taken as a hypothesis. -/
def Execution.Static {μ κ : Type*} {P : Protocol ValidatorIndex μ (Store preset fork) κ}
    {J : Set ValidatorIndex} (ref : BeaconState preset fork) (e : Execution P J) : Prop :=
  ∀ n, ∀ u ∈ J, StaticStore J ref ((e.world n).state u)

end Models.Network

end EthLib.Consensus
