module

public import EthLib.Consensus.Proofs.DirectSafety.Attestations
public import EthLib.Consensus.Proofs.Models.Stake
public import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Validator identities and weights

Keys, not branch-local indices, identify the validators in the conclusion.

The reference registry counts each key once; this is proved from genesis, not assumed silently.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The keys of the validators at the given indices, where the registry has them. -/
noncomputable def keysAt {fork : Fork} (state : BeaconState preset fork)
    (indices : List ValidatorIndex) : Finset BLSPubkey := by
  classical
  exact (indices.filterMap fun i => (state.validators.data[i.toNat]?).map (·.pubkey)).toFinset

/-- The keys of the validators active at the current epoch of the state. -/
noncomputable def activeKeys {fork : Fork} (state : BeaconState preset fork) : Finset BLSPubkey :=
  keysAt state (getActiveValidatorIndices state (getCurrentEpoch state))

/-- The effective balance of the first validator with the key, in Gwei, or zero. -/
def effectiveWeight {fork : Fork} (state : BeaconState preset fork) (key : BLSPubkey) : Nat :=
  ((state.validators.data.toList.find? fun v => v.pubkey == key).map
    (·.effectiveBalance.toNat)).getD 0

/-- A genesis state built from deposits has distinct validator keys. -/
theorem genesis_unique {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) : PubkeysDistinct g.state := by
  obtain ⟨_, _, _, ok⟩ := genesis
  exact (validatorKeys_prefix_and_distinct_of_genesis_chainSteps ok
    (last := g) .refl).2

/-- A run keeps distinct validator keys distinct. -/
theorem _root_.EthLib.Consensus.Run.unique {g a : ForkedBeaconState preset}
    (run : Run config checks g a)
    (initial : PubkeysDistinct g.state) : PubkeysDistinct a.state :=
  (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).2 initial

/-- A run keeps the key of each validator at its position. -/
theorem _root_.EthLib.Consensus.Run.key_preserved {g a : ForkedBeaconState preset}
    (run : Run config checks g a)
    (i : Nat) (old : Validator) (found : g.state.validators.data[i]? = some old) :
    ∃ current, a.state.validators.data[i]? = some current ∧ current.pubkey = old.pubkey := by
  exact validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).1 found

private theorem key_preserved_from_member {g a before after : ForkedBeaconState preset}
    {run : Run config checks g a} {step : Step config checks before after}
    (member : run.Contains step) (i : Nat) (old : Validator)
    (found : before.state.validators.data[i]? = some old) :
    ∃ current, a.state.validators.data[i]? = some current ∧ current.pubkey = old.pubkey := by
  induction member with
  | last pre step => exact (Run.nil.snoc step).key_preserved i old found
  | earlier member next ih =>
    obtain ⟨middle, foundMiddle, same⟩ := ih found
    obtain ⟨current, foundCurrent, lastSame⟩ :=
      (Run.nil.snoc next).key_preserved i middle foundMiddle
    exact ⟨current, foundCurrent, lastSame.trans same⟩

/-- A vote of the run at an index is accepted under the key that the last state has there.

The index is read in the registry of the run itself, before the block of the vote. -/
theorem selected_vote_key {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (i : ValidatorIndex) (data : AttestationData)
    (v : Validator) (found : a.state.validators.data[i.toNat]? = some v)
    (voted : (i, data) ∈ run.votes) : run.Accepted v.pubkey data := by
  obtain ⟨before, after, step, member, vote⟩ := voted
  have atStart : ∃ old, before.state.validators.data[i.toNat]? = some old := by
    cases step with
    | slot ok => exact False.elim vote
    | block engine signed due ok =>
      rename_i fork before after
      obtain ⟨attestation, _, _, indices, computed, inIndices⟩ := vote
      have active := mem_getActiveValidatorIndices_of_getAttestingIndices computed inIndices
      simp only [getActiveValidatorIndices, List.mem_filterMap, List.mem_zipIdx_iff_getElem?,
        Prod.exists, Option.ite_none_right_eq_some, Option.some.injEq] at active
      obtain ⟨v, position, found, _, equal⟩ := active
      have bound : position < before.validators.data.size := by
        simpa using (List.getElem?_eq_some_iff.mp found).1
      -- Even a wrapped index is below the position that produced it.
      have small : i.toNat < before.validators.data.size := by
        subst equal
        exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) bound
      exact ⟨before.validators.data[i.toNat], by simp [small]⟩
  obtain ⟨old, oldFound⟩ := atStart
  obtain ⟨current, currentFound, same⟩ := key_preserved_from_member member i.toNat old oldFound
  have equal : current = v := Option.some.inj (currentFound.symm.trans found)
  exact ⟨before, after, step, member, i, old, vote, oldFound, by simpa [equal] using same.symm⟩

/-- The stake of the keys at some indices is the sum of the effective balances at those indices.

The keys of the registry must be distinct, and the indices inside it. -/
theorem keys_weight {fork : Fork} (state : BeaconState preset fork)
    (indices : List ValidatorIndex) (unique : PubkeysDistinct state)
    (inside : ∀ i ∈ indices, i.toNat < state.validators.data.size) :
    Models.stake (effectiveWeight state) (keysAt state indices) =
      ∑ i ∈ indices.toFinset,
        ((state.validators.data[i.toNat]?).map (·.effectiveBalance.toNat)).getD 0 := by
  classical
  have lookup (vs : List Validator) (distinct : (vs.map (·.pubkey)).Nodup)
      (v : Validator) (member : v ∈ vs) :
      vs.find? (fun w => w.pubkey == v.pubkey) = some v := by
    induction vs with
    | nil => simp at member
    | cons w ws ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : w.pubkey ≠ v.pubkey := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨v, member, same.symm⟩)
        simp [different, ih distinct.2 member]
  let key (i : ValidatorIndex) (hi : i ∈ indices.toFinset) : BLSPubkey :=
    (state.validators.data[i.toNat]'(inside i (List.mem_toFinset.mp hi))).pubkey
  -- Distinct registry keys make the index-to-key map a bijection on the selected set.
  unfold Models.stake
  symm
  apply Finset.sum_bij key
  · intro i hi
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, List.mem_toFinset.mp hi, by simp [key,
      inside i (List.mem_toFinset.mp hi)]⟩
  · intro i hi j hj same
    apply UInt64.toNat_inj.mp
    apply unique.eq_of_getElem_eq
      (by simpa [validatorKeys] using inside i (List.mem_toFinset.mp hi))
      (by simpa [validatorKeys] using inside j (List.mem_toFinset.mp hj))
    simpa [validatorKeys, key] using same
  · intro k hk
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at hk
    obtain ⟨i, hi, found⟩ := hk
    exact ⟨i, List.mem_toFinset.mpr hi, by
      simpa [key, Array.getElem?_eq_getElem, inside i hi] using found⟩
  · intro i hi
    have member : state.validators.data[i.toNat]'(inside i (List.mem_toFinset.mp hi)) ∈
        state.validators.data.toList := by
      simp
    simp [effectiveWeight, key, lookup _ unique _ member,
      inside i (List.mem_toFinset.mp hi)]

end EthLib.Consensus.DirectSafety
