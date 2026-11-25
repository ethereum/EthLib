module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori
public import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Cohorts
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# Proofs: how far the stake of honest validators moves in a window of epochs

Between two states, rewards, penalties, deposits and withdrawals move effective balances.

Honest validators with two thirds of the active stake and a margin keep two thirds in the window.

This holds at every fork from Altair until Gloas, while no active validator becomes slashed.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models DirectSafety DirectSafety.Apriori

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The active stake that the slashed validators of a state may add later, beyond their stake now.

A slashed validator active at the state counts its cap there, less its effective balance.

A slashed validator not active there counts its whole cap. -/
def slashedHeadroom (x : ForkedBeaconState preset) : ℕ :=
  ∑ i ∈ Finset.range x.state.validators.data.size,
    ((x.state.validators.data[i]?).map fun v =>
      if v.slashed then
        (withdrawalMaxEffectiveBalance preset x.fork v).toNat -
          (if isActiveValidator v (getCurrentEpoch x.state) then v.effectiveBalance.toNat else 0)
      else 0).getD 0

/-- The stake margin of a window up to epoch `high + 1`, read at its first state.

The drift leaves out the slashed validators, so the margin also charges their room below their caps.

It is twice the a priori drift and twice the room of the slashed validators below their caps. -/
noncomputable def stakeMargin (config : Config) (x : ForkedBeaconState preset) (high : ℕ) : ℕ :=
  2 * drift (config := config) x high + 2 * slashedHeadroom x

/-- Along a run, a registry position keeps its key. -/
private theorem pubkey_eq_of_run {x w : ForkedBeaconState preset}
    (tail : Run config checks x w) {i : Nat} {vx vw : Validator}
    (fx : x.state.validators.data[i]? = some vx) (fw : w.state.validators.data[i]? = some vw) :
    vx.pubkey = vw.pubkey := by
  obtain ⟨current, read, key⟩ := validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 fx
  rw [fw] at read
  cases read
  exact key.symm

/-- Before Gloas, an active index names a validator of the registry. -/
private theorem found_of_active {s : ForkedBeaconState preset} (early : s.fork < .glamsterdam)
    {i : ValidatorIndex}
    (member : i ∈ getActiveValidatorIndices s.state (getCurrentEpoch s.state)) :
    ∃ v, s.state.validators.data[i.toNat]? = some v :=
  let ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (s.state.validators.bound early)).mp member
  ⟨v, found⟩

/-- The key of a validator at a listed index is among the keys at those indices. -/
private theorem mem_keysAt {fork : Fork} {s : BeaconState preset fork}
    {indices : List ValidatorIndex} {i : ValidatorIndex} (member : i ∈ indices) {v : Validator}
    (found : s.validators.data[i.toNat]? = some v) : v.pubkey ∈ keysAt s indices := by
  simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
  exact ⟨i, member, by simp [found]⟩

/-- A validator slashed at `x` stays within its cap at `x`, when a slashing assigns an exit. -/
private theorem slashed_effective_le_cap {g x w : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x w)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : w.fork < .glamsterdam) (regime : .pectra ≤ x.fork ∨ w.fork < .pectra)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) {i : Nat} {vx vw : Validator}
    (fx : x.state.validators.data[i]? = some vx) (fw : w.state.validators.data[i]? = some vw)
    (slashed : vx.slashed = true) :
    vw.effectiveBalance.toNat ≤ (withdrawalMaxEffectiveBalance preset x.fork vx).toNat := by
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  -- The slashing assigned an exit, so the credentials of the validator stay as they were.
  have assigned := run_slashed_exit_assigned shared genesis caps.activation caps.compounding
    delay i vx fx slashed
  obtain ⟨u, read, credentials⟩ := tail.compounding_of_exit_assigned caps.activation
    caps.compounding i vx fx assigned
  rw [fw] at read
  cases read
  have cap := (shared.append tail).effectiveBalance_capped genesis caps.activation
    caps.compounding vw (Array.mem_of_getElem? fw)
  -- The cap at `w` is at most the cap at `x`, on either side of Electra.
  have kept : withdrawalMaxEffectiveBalance preset w.fork vw ≤
      withdrawalMaxEffectiveBalance preset x.fork vx := by
    rcases regime with electra | before
    · have later : Fork.pectra ≤ w.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
      simp only [withdrawalMaxEffectiveBalance, later, electra, ↓reduceIte,
        getMaxEffectiveBalance]
      by_cases compound : hasCompoundingWithdrawalCredential vw = true
      · simp only [compound, credentials compound, ↓reduceIte]
        exact UInt64.le_refl _
      · simp only [compound, Bool.false_eq_true, ↓reduceIte]
        split
        · exact caps.compounding
        · exact UInt64.le_refl _
    · have xBefore := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) before
      have wNot : ¬ Fork.pectra ≤ w.fork := Nat.not_le_of_gt before
      have xNot : ¬ Fork.pectra ≤ x.fork := Nat.not_le_of_gt xBefore
      simp only [withdrawalMaxEffectiveBalance, wNot, xNot, ↓reduceIte]
      exact UInt64.le_refl _
  exact (UInt64.le_iff_toNat_le.mp cap).trans (UInt64.le_iff_toNat_le.mp kept)

/-- Before Gloas, the caps of the slashed entries are their active stake and their room. -/
private theorem slashedCaps_le {x : ForkedBeaconState preset} (early : x.fork < .glamsterdam) :
    ∑ n ∈ Finset.range x.state.validators.data.size,
      ((x.state.validators.data[n]?).map fun v =>
        if v.slashed then (withdrawalMaxEffectiveBalance preset x.fork v).toNat else 0).getD 0 ≤
    ∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset with
        (x.state.validators.data[i.toNat]?).map (·.slashed) = some true,
      balanceAt x.state i.toNat + slashedHeadroom x := by
  classical
  -- The part of each cap that the entry holds while active and slashed.
  let held : ℕ → ℕ := fun n => ((x.state.validators.data[n]?).map fun v =>
    if v.slashed then
      (if isActiveValidator v (getCurrentEpoch x.state) then v.effectiveBalance.toNat else 0)
    else 0).getD 0
  have within := x.state.validators.bound early
  calc _ ≤ ∑ n ∈ Finset.range x.state.validators.data.size, (held n +
        ((x.state.validators.data[n]?).map fun v =>
          if v.slashed then
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat -
              (if isActiveValidator v (getCurrentEpoch x.state) then v.effectiveBalance.toNat
                else 0)
          else 0).getD 0) := by
        refine Finset.sum_le_sum fun n _ => ?_
        simp only [held]
        cases x.state.validators.data[n]? with
        | none => simp
        | some v =>
          simp only [Option.map_some, Option.getD_some]
          split
          · exact le_add_tsub
          · simp
    _ = _ + slashedHeadroom x := Finset.sum_add_distrib
    _ ≤ _ := by
      refine Nat.add_le_add_right ?_ _
      -- Only a slashed active entry holds anything, and it is a slashed active index.
      refine (Finset.sum_le_sum_of_ne_zero (t := (
        (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset.filter
          (fun i => (x.state.validators.data[i.toNat]?).map (·.slashed) = some true)).image
            UInt64.toNat) fun n inside nonzero => ?_).trans (le_of_eq ?_)
      · have small := Finset.mem_range.mp inside
        obtain ⟨v, found⟩ : ∃ v, x.state.validators.data[n]? = some v :=
          ⟨_, Array.getElem?_eq_getElem small⟩
        simp only [held, found, Option.map_some, Option.getD_some] at nonzero
        have flag : v.slashed = true := by
          by_contra clean
          simp [clean] at nonzero
        have active : isActiveValidator v (getCurrentEpoch x.state) = true := by
          by_contra idle
          simp [flag, idle] at nonzero
        have fits : n < UInt64.size := Nat.lt_of_lt_of_le small
          (within.trans (Nat.le_of_lt (UInt64.toNat_lt_size _)))
        have back := UInt64.toNat_ofNat_of_lt' fits
        refine Finset.mem_image.mpr ⟨UInt64.ofNat n, Finset.mem_filter.mpr ⟨?_, ?_⟩, back⟩
        · exact List.mem_toFinset.mpr ((mem_getActiveValidatorIndices within).mpr
            ⟨v, by rw [back]; exact found, active⟩)
        · simp [back, found, flag]
      · rw [Finset.sum_image fun i _ j _ same => UInt64.toNat_inj.mp same]
        refine Finset.sum_congr rfl fun i member => ?_
        obtain ⟨active, flag⟩ := Finset.mem_filter.mp member
        obtain ⟨v, found, live⟩ :=
          (mem_getActiveValidatorIndices within).mp (List.mem_toFinset.mp active)
        have marked : v.slashed = true := by simpa [found] using flag
        simp [held, balanceAt, found, marked, live]

/-- Before Gloas, the unslashed active indices weigh at most the recent keys of the state. -/
private theorem unslashed_le_recentKeys {g w : ForkedBeaconState preset}
    (run : Run config checks g w) (genesis : Genesis (config := config) (checks := checks) g)
    (early : w.fork < .glamsterdam) :
    ∑ i ∈ (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset with
        ¬ (w.state.validators.data[i.toNat]?).map (·.slashed) = some true,
      balanceAt w.state i.toNat ≤ stake (effectiveWeight w.state) (recentKeys w.state) := by
  classical
  have dw := run.pubkeysDistinct genesis
  -- Each unslashed active index is charged to its key, which is recent.
  let key : ValidatorIndex → Cryptography.Bls.BLSPubkey := fun i =>
    ((w.state.validators.data[i.toNat]?).map (·.pubkey)).getD default
  have facts : ∀ i ∈ (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset.filter
      (fun i => ¬ (w.state.validators.data[i.toNat]?).map (·.slashed) = some true),
      ∃ v, w.state.validators.data[i.toNat]? = some v ∧ v.slashed = false ∧
        i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state) := by
    intro i member
    obtain ⟨active, flag⟩ := Finset.mem_filter.mp member
    have active := List.mem_toFinset.mp active
    obtain ⟨v, found⟩ := found_of_active early active
    exact ⟨v, found, by simpa [found] using flag, active⟩
  refine Finset.sum_le_sum_of_injOn key ?_ ?_ ?_ (fun _ _ _ => Nat.zero_le _)
  · intro i member j other same
    obtain ⟨vi, fi, _⟩ := facts i member
    obtain ⟨vj, fj, _⟩ := facts j other
    simp only [key, fi, fj, Option.map_some, Option.getD_some] at same
    exact UInt64.toNat_inj.mp (dw.index_eq fi fj same)
  · intro k image
    obtain ⟨i, member, rfl⟩ := Finset.mem_image.mp image
    obtain ⟨v, found, flag, active⟩ := facts i member
    have keyEq : key i = v.pubkey := by simp [key, found]
    rw [keyEq]
    unfold recentKeys activeKeys
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_union_left _ (mem_keysAt active found),
      not_slashedAt dw (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)) flag⟩
  · intro i member
    obtain ⟨v, found, _⟩ := facts i member
    have keyEq : key i = v.pubkey := by simp [key, found]
    rw [keyEq,
      effectiveWeight_of_member dw (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))]
    simp [balanceAt, found]

/-- Before Gloas, the unslashed keys of a state weigh at most its unslashed active indices. -/
private theorem unslashedKeys_le {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) :
    stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
      ∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset with
        ¬ (x.state.validators.data[i.toNat]?).map (·.slashed) = some true,
      balanceAt x.state i.toNat := by
  classical
  have dx := run.pubkeysDistinct genesis
  let key : ValidatorIndex → Cryptography.Bls.BLSPubkey := fun i =>
    ((x.state.validators.data[i.toNat]?).map (·.pubkey)).getD default
  -- Each unslashed key is the key of an unslashed active index.
  have covered : unslashedKeys x.state ⊆
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset.filter
        (fun i => ¬ (x.state.validators.data[i.toNat]?).map (·.slashed) = some true)).image
          key := by
    intro k member
    unfold unslashedKeys activeKeys keysAt at member
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filterMap,
      Option.map_eq_some_iff] at member
    obtain ⟨⟨i, active, v, found, rfl⟩, clean⟩ := member
    have flag : v.slashed = false := by
      cases marked : v.slashed
      · rfl
      · exact absurd ⟨v, Array.mem_toList_iff.mpr (Array.mem_of_getElem? found), rfl, marked⟩ clean
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr active, ?_⟩, ?_⟩
    · simp [found, flag]
    · simp [key, found]
  -- The map to keys is injective on indices that name validators.
  have injective : Set.InjOn key
      ↑((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset.filter
        (fun i => ¬ (x.state.validators.data[i.toNat]?).map (·.slashed) = some true)) := by
    intro i member j other same
    obtain ⟨vi, fi⟩ := found_of_active early
      (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
    obtain ⟨vj, fj⟩ := found_of_active early
      (List.mem_toFinset.mp (Finset.mem_filter.mp other).1)
    simp only [key, fi, fj, Option.map_some, Option.getD_some] at same
    exact UInt64.toNat_inj.mp (dx.index_eq fi fj same)
  refine (Finset.sum_le_sum_of_subset covered).trans (le_of_eq ?_)
  rw [Finset.sum_image injective]
  refine Finset.sum_congr rfl fun i member => ?_
  obtain ⟨v, found⟩ := found_of_active early
    (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
  simp only [key, found, Option.map_some, Option.getD_some]
  rw [effectiveWeight_of_member dx (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))]
  simp [balanceAt, found]

/-- Honest stake falls by at most the stake that the drift says unslashed keys lose.

A run from a genesis state reaches `x`, and a branch continues it to `w`, before Gloas.

Each honest validator is active at `x`, and active and unslashed at `w`. -/
theorem stake_le_add_referenceLoss {g x w : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x w)
    (genesis : Genesis (config := config) (checks := checks) g) (early : w.fork < .glamsterdam)
    {honest : Finset ValidatorIndex}
    (active : ∀ i ∈ honest, i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state))
    (unslashed : ∀ i ∈ honest, (w.state.validators.data[i.toNat]?).map (·.slashed) = some false)
    (activeBefore : ∀ i ∈ honest, i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state)) :
    stake (fun i => balanceAt x.state i.toNat) honest ≤
      stake (fun i => balanceAt w.state i.toNat) honest + referenceLoss x w := by
  classical
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have dx := shared.pubkeysDistinct genesis
  have dw := (shared.append tail).pubkeysDistinct genesis
  -- Each honest index names an unslashed validator at both states, with one key.
  have facts : ∀ i ∈ honest, ∃ vx vw, x.state.validators.data[i.toNat]? = some vx ∧
      w.state.validators.data[i.toNat]? = some vw ∧ vx.pubkey = vw.pubkey ∧
      vx.slashed = false ∧ vw.slashed = false := by
    intro i member
    obtain ⟨vw, fw⟩ := found_of_active early (active i member)
    obtain ⟨vx, fx⟩ := found_of_active xEarly (activeBefore i member)
    have flag : vw.slashed = false := by simpa [fw] using unslashed i member
    refine ⟨vx, vw, fx, fw, pubkey_eq_of_run tail fx fw, ?_, flag⟩
    -- A slashed flag at `x` would stay set at `w`.
    cases old : vx.slashed
    · rfl
    · obtain ⟨u, read, marked⟩ := tail.slashedPersistence _ vx fx old
      rw [fw] at read
      cases read
      simp [flag] at marked
  -- Each honest index is charged to its key, which the loss counts once.
  let key : ValidatorIndex → Cryptography.Bls.BLSPubkey := fun i =>
    ((w.state.validators.data[i.toNat]?).map (·.pubkey)).getD default
  have charged : ∑ i ∈ honest, (balanceAt x.state i.toNat - balanceAt w.state i.toNat) ≤
      referenceLoss x w := by
    unfold referenceLoss
    refine Finset.sum_le_sum_of_injOn key ?_ ?_ ?_ (fun _ _ _ => Nat.zero_le _)
    · intro i member j other same
      obtain ⟨_, vi, _, fi, _⟩ := facts i member
      obtain ⟨_, vj, _, fj, _⟩ := facts j other
      simp only [key, fi, fj, Option.map_some, Option.getD_some] at same
      exact UInt64.toNat_inj.mp (dw.index_eq fi fj same)
    · -- The key is unslashed at both states, and active at `x`.
      intro k image
      obtain ⟨i, member, rfl⟩ := Finset.mem_image.mp image
      obtain ⟨vx, vw, fx, fw, same, flagx, flagw⟩ := facts i member
      have keyEq : key i = vw.pubkey := by simp [key, fw]
      rw [keyEq, Finset.mem_filter]
      refine ⟨?_, not_slashedAt dw (Array.mem_toList_iff.mpr (Array.mem_of_getElem? fw)) flagw⟩
      unfold unslashedKeys activeKeys
      rw [Finset.mem_filter, ← same]
      exact ⟨mem_keysAt (activeBefore i member) fx,
        not_slashedAt dx (Array.mem_toList_iff.mpr (Array.mem_of_getElem? fx)) flagx⟩
    · -- The key weighs its effective balance at each state, and it is recent at `w`.
      intro i member
      obtain ⟨vx, vw, fx, fw, same, flagx, flagw⟩ := facts i member
      have keyEq : key i = vw.pubkey := by simp [key, fw]
      have recent : vw.pubkey ∈ recentKeys w.state := by
        unfold recentKeys activeKeys
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_union_left _ (mem_keysAt (active i member) fw),
          not_slashedAt dw (Array.mem_toList_iff.mpr (Array.mem_of_getElem? fw)) flagw⟩
      simp only [keyEq, supported, recent, ↓reduceIte]
      rw [effectiveWeight_of_member dw (Array.mem_toList_iff.mpr (Array.mem_of_getElem? fw)),
        ← same,
        effectiveWeight_of_member dx (Array.mem_toList_iff.mpr (Array.mem_of_getElem? fx))]
      simp [balanceAt, fx, fw]
  calc stake (fun i => balanceAt x.state i.toNat) honest
      ≤ ∑ i ∈ honest, (balanceAt w.state i.toNat +
          (balanceAt x.state i.toNat - balanceAt w.state i.toNat)) :=
        Finset.sum_le_sum fun i _ => by omega
    _ = stake (fun i => balanceAt w.state i.toNat) honest +
          ∑ i ∈ honest, (balanceAt x.state i.toNat - balanceAt w.state i.toNat) :=
        Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left charged _

/-- Active stake rises by at most the gain that the drift charges and the slashed headroom.

A run from a genesis state reaches `x`, and a branch continues it to `w`, before Gloas.

Both states are from Electra, or both are before it, and the preset orders its caps.

The withdrawal delay is positive.

Every validator active and slashed at `w` was slashed at `x`. -/
theorem activeStake_le_add_referenceGain {g x w : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x w)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    -- A positive withdrawal delay makes a slashing assign an exit.
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : w.fork < .glamsterdam) (regime : .pectra ≤ x.fork ∨ w.fork < .pectra)
    (noSlashing : ∀ i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state),
      (w.state.validators.data[i.toNat]?).map (·.slashed) = some true →
        (x.state.validators.data[i.toNat]?).map (·.slashed) = some true) :
    stake (fun i => balanceAt w.state i.toNat)
        (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset ≤
      stake (fun i => balanceAt x.state i.toNat)
          (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset +
        referenceGain x w + slashedHeadroom x := by
  classical
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  -- The unslashed active stake at `w` is within the recent keys, so within the gain.
  have unslashedPart :
      ∑ i ∈ (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset with
          ¬ (w.state.validators.data[i.toNat]?).map (·.slashed) = some true,
        balanceAt w.state i.toNat ≤
      ∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset with
          ¬ (x.state.validators.data[i.toNat]?).map (·.slashed) = some true,
        balanceAt x.state i.toNat + referenceGain x w := by
    have recent := unslashed_le_recentKeys (shared.append tail) genesis early
    have keys := unslashedKeys_le shared genesis xEarly
    have gained : stake (effectiveWeight w.state) (recentKeys w.state) ≤
        stake (effectiveWeight x.state) (unslashedKeys x.state) + referenceGain x w := by
      unfold stake referenceGain
      calc ∑ k ∈ recentKeys w.state, effectiveWeight w.state k
          ≤ ∑ k ∈ recentKeys w.state,
              (supported (unslashedKeys x.state) (effectiveWeight x.state) k +
                (effectiveWeight w.state k -
                  supported (unslashedKeys x.state) (effectiveWeight x.state) k)) :=
            Finset.sum_le_sum fun k _ => by omega
        _ = _ := Finset.sum_add_distrib
        _ ≤ _ := by
          refine Nat.add_le_add_right ?_ _
          -- The supported weight counts only the recent keys among the unslashed keys.
          simp only [supported]
          rw [Finset.sum_ite_mem]
          exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
    omega
  -- A slashed active index at `w` rises at most to its cap at `x`, which the headroom counts.
  have slashedPart :
      ∑ i ∈ (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset with
          (w.state.validators.data[i.toNat]?).map (·.slashed) = some true,
        balanceAt w.state i.toNat ≤
      ∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset with
          (x.state.validators.data[i.toNat]?).map (·.slashed) = some true,
        balanceAt x.state i.toNat + slashedHeadroom x := by
    -- Each such index names a slashed entry at `x`, whose cap bounds its balance at `w`.
    let cap : ℕ → ℕ := fun n => ((x.state.validators.data[n]?).map fun v =>
      if v.slashed then (withdrawalMaxEffectiveBalance preset x.fork v).toNat else 0).getD 0
    have charged : ∀ i ∈ (getActiveValidatorIndices w.state
        (getCurrentEpoch w.state)).toFinset.filter
          (fun i => (w.state.validators.data[i.toNat]?).map (·.slashed) = some true),
        ∃ v, x.state.validators.data[i.toNat]? = some v ∧
          balanceAt w.state i.toNat ≤ cap i.toNat := by
      intro i member
      obtain ⟨active, flag⟩ := Finset.mem_filter.mp member
      have active := List.mem_toFinset.mp active
      obtain ⟨vw, fw⟩ := found_of_active early active
      obtain ⟨vx, fx, marked⟩ := Option.map_eq_some_iff.mp (noSlashing i active flag)
      have bound := slashed_effective_le_cap shared tail genesis caps early regime delay
        fx fw marked
      refine ⟨vx, fx, ?_⟩
      simp only [cap, balanceAt, fx, fw, marked, Option.map_some, Option.getD_some, ↓reduceIte]
      exact bound
    refine le_trans ?_ (slashedCaps_le xEarly)
    refine Finset.sum_le_sum_of_injOn UInt64.toNat
      (fun i _ j _ same => UInt64.toNat_inj.mp same) ?_ ?_ (fun _ _ _ => Nat.zero_le _)
    · intro n image
      obtain ⟨i, member, rfl⟩ := Finset.mem_image.mp image
      obtain ⟨v, found, _⟩ := charged i member
      exact Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1
    · intro i member
      obtain ⟨_, _, bound⟩ := charged i member
      exact bound
  -- Split the active indices of each state by their slashed flags.
  unfold stake
  rw [← Finset.sum_filter_add_sum_filter_not
      (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset
      (fun i => (w.state.validators.data[i.toNat]?).map (·.slashed) = some true),
    ← Finset.sum_filter_add_sum_filter_not
      (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset
      (fun i => (x.state.validators.data[i.toNat]?).map (·.slashed) = some true)]
  omega

/-- Honest validators with two thirds of the active stake and the margin keep two thirds later.

A run from a genesis state `g` reaches `x`, and a branch continues it to `w`, before Gloas.

The preset meets the parameters of the a priori drift, as its accountable safety asks.

The epoch of `w` is at most `high + 1`, and the guard of the drift holds at `x` and `high`.

Each honest validator is active at `x`, and active and unslashed at `w`.

Every validator active and slashed at `w` was slashed at `x`.

At `x`, three times the honest stake covers twice the active stake and the margin of the window.

Then at `w`, three times the honest stake is at least twice the active stake. -/
theorem quorum_of_stakeMargin {g x w : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x w)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (early : w.fork < .glamsterdam) {high : ℕ}
    (window : (getCurrentEpoch w.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) {honest : Finset ValidatorIndex}
    (active : ∀ i ∈ honest, i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state))
    (unslashed : ∀ i ∈ honest, (w.state.validators.data[i.toNat]?).map (·.slashed) = some false)
    (activeBefore : ∀ i ∈ honest, i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state))
    (noSlashing : ∀ i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state),
      (w.state.validators.data[i.toNat]?).map (·.slashed) = some true →
        (x.state.validators.data[i.toNat]?).map (·.slashed) = some true)
    (margin : 2 * stake (fun i => balanceAt x.state i.toNat)
          (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset +
        stakeMargin config x high ≤
      3 * stake (fun i => balanceAt x.state i.toNat) honest) :
    2 * stake (fun i => balanceAt w.state i.toNat)
        (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset ≤
      3 * stake (fun i => balanceAt w.state i.toNat) honest := by
  have lost := stake_le_add_referenceLoss shared tail genesis early active unslashed activeBefore
  -- The guard keeps the whole window on one side of Electra.
  have regime := Internal.regime_of_supported shared tail
    ⟨genesis, parameters, caps, aligned, early, window, guard⟩
  -- The guard asks for a withdrawal delay of at least two epochs.
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    have := guard.2.2.2.2.2.2.2.2.2.1
    omega
  have gained := activeStake_le_add_referenceGain shared tail genesis caps delay early regime
    noSlashing
  -- The a priori drift of accountable safety bounds the movement, from the first state alone.
  have drifted := stateDrift_le_drift shared tail genesis parameters caps aligned twoSlots early
    window guard
  unfold stateDrift at drifted
  unfold stakeMargin at margin
  omega

end EthLib.Consensus
