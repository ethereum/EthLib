module

public import EthLib.Consensus.Proofs.Transition.BlockCredits
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Operations
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.Totality.FlagsActive
import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock
import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.PayloadInputs
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts
import EthLib.Consensus.Proofs.Transition.Withdrawals
import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
import EthLib.Consensus.Proofs.Participation

/-!
# The balances along a branch inside one epoch

A tally follows the blocks of a run inside one epoch, from Fulu.

It reads every balance change of the run from its last state.

Withdrawals and conversions debit a counted set.

The sync committee moves each member by its seats.

The other credits go to the proposers of the blocks and to the recipients of deposits.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

open BlockLedger BlockCredits

/-! ### The blocks of one epoch -/

section Epoch

variable {fork : Fork}

/-- A later state of the same epoch.

Its registry grows and keeps activity and effective balances. -/
private structure Within (a s : BeaconState preset fork) : Prop where
  size : a.validators.data.size ≤ s.validators.data.size
  epoch : getCurrentEpoch s = getCurrentEpoch a
  active : ActiveKept (activityFixedEpoch a) a s
  effective : EffectiveKept a s

/-- Every state is within its own epoch. -/
private theorem Within.refl (a : BeaconState preset fork) : Within a a :=
  ⟨Nat.le_refl _, rfl, ActiveKept.refl _ _, effectiveKept_refl _⟩

/-- A steady step stays within the epoch. -/
private theorem Within.steady {a s t : BeaconState preset fork} (w : Within a s)
    (kept : Steady s t) : Within a t where
  size := Nat.le_trans w.size kept.keeps.1
  epoch := kept.epoch.trans w.epoch
  active := by
    have fixed : activityFixedEpoch s = activityFixedEpoch a := by
      simp only [activityFixedEpoch, w.epoch]
    have step := kept.keeps.2.2
    rw [fixed] at step
    exact w.active.trans step
  effective := effectiveKept_trans w.effective kept.effective w.size

/-- The effective balances below the registry size of the start, read as options. -/
private theorem Within.effective_map {a s : BeaconState preset fork} (w : Within a s) (j : ℕ)
    (inside : j < a.validators.data.size) :
    (a.validators.data[j]?).map (·.effectiveBalance) =
      (s.validators.data[j]?).map (·.effectiveBalance) := by
  have same := w.effective j inside
  have later : j < s.validators.data.size := Nat.lt_of_lt_of_le inside w.size
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem later,
    Option.map_some, Option.getD_some] at same ⊢
  exact congrArg some (UInt64.toNat_inj.mp same.symm)

/-- A state within the epoch has the total active balance of the start. -/
private theorem Within.activeBalanceTotal {a s : BeaconState preset fork} (w : Within a s) :
    activeBalanceTotal s = activeBalanceTotal a :=
  activeBalanceTotal_eq w.epoch w.active w.effective w.size

/-- A state within the epoch reads the total of the start, with its errors. -/
private theorem Within.total {a s : BeaconState preset fork} (w : Within a s) :
    getTotalActiveBalance s = getTotalActiveBalance a :=
  DirectSafety.total_active_congr
    (w.active.mono (getCurrentEpoch_le_activityFixedEpoch a)) w.epoch w.effective

/-- A state within the epoch reads the participant reward of the start. -/
private theorem Within.read {a s : BeaconState preset fork} (w : Within a s) :
    SyncRewardRead s ↔ SyncRewardRead a := by
  unfold SyncRewardRead
  rw [syncParticipantReward_congr w.total]

/-- A state within the epoch has the recent validators of the start. -/
private theorem Within.recent {a s : BeaconState preset fork} (w : Within a s) (i : ℕ) :
    (isActiveAt s (getPreviousEpoch s) i = true ∨ isActiveAt s (getCurrentEpoch s) i = true) ↔
      (isActiveAt a (getPreviousEpoch a) i = true ∨ isActiveAt a (getCurrentEpoch a) i = true) := by
  have previous : getPreviousEpoch s = getPreviousEpoch a := by
    unfold getPreviousEpoch; rw [w.epoch]
  have fixed := getCurrentEpoch_le_activityFixedEpoch a
  have previousLe : getPreviousEpoch a ≤ activityFixedEpoch a :=
    UInt64.le_trans (getPreviousEpoch_le a) fixed
  rw [previous, w.epoch, w.active _ previousLe, w.active _ fixed]

/-- The base rewards read at the start are read at every state within the epoch. -/
private theorem Within.reads {a s : BeaconState preset fork} (w : Within a s) {base : ℕ → ℕ}
    (reads : Reads a base) : Reads s base := by
  intro index total reward recent totalOk rewardOk
  rw [w.recent] at recent
  have inside := lt_size_of_isActiveAt_recent recent
  rw [w.activeBalanceTotal] at totalOk
  rw [← getBaseReward_congr inside (w.effective_map _ inside)] at rewardOk
  exact reads index total reward recent totalOk rewardOk

/-- The base rewards read at a state within the epoch are read at the start. -/
private theorem Within.reads_back {a s : BeaconState preset fork} (w : Within a s)
    {base : ℕ → ℕ} (reads : Reads s base) : Reads a base := by
  intro index total reward recent totalOk rewardOk
  have inside := lt_size_of_isActiveAt_recent recent
  refine reads index total reward ((w.recent _).mpr recent)
    (by rw [w.activeBalanceTotal]; exact totalOk) ?_
  rw [← getBaseReward_congr inside (w.effective_map _ inside)]
  exact rewardOk

/-- Whether the validator at an index is slashed, and false outside the registry. -/
private def slashedAt (s : BeaconState preset fork) (v : ValidatorIndex) : Bool :=
  ((s.validators.data[v.toNat]?).map (·.slashed)).getD false

/-- The initial slashing penalty of a slashed validator, read at its effective balance. -/
private def slashBackAt (s : BeaconState preset fork) (v : ValidatorIndex) : ℕ :=
  if slashedAt s v then effectiveAt ⟨fork, s⟩ v.toNat /
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0

/-- The sync amount of a validator for one block, its seats times a participant reward. -/
private def syncAt (s : BeaconState preset fork) (reward : ℕ) (v : ValidatorIndex) : ℕ :=
  if altair : .altair ≤ fork then syncSeats s altair v.toNat * reward else 0

/-- A slashed validator stays slashed along a frame. -/
private theorem slashedAt_of_frame {s t : BeaconState preset fork} (frame : Frame s t)
    {v : ValidatorIndex} (marked : slashedAt s v = true) : slashedAt t v = true := by
  unfold slashedAt at marked ⊢
  cases found : s.validators.data[v.toNat]? with
  | none => simp [found] at marked
  | some old =>
    simp only [found, Option.map_some, Option.getD_some] at marked
    have later : v.toNat < t.validators.data.size :=
      Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 frame.registryGrows
    rw [Array.getElem?_eq_getElem later]
    simpa using frame.slashed v.toNat old _ found (Array.getElem?_eq_getElem later) marked

/-- A slashed validator is in the registry. -/
private theorem inside_of_slashedAt {s : BeaconState preset fork} {v : ValidatorIndex}
    (marked : slashedAt s v = true) : v.toNat < s.validators.data.size := by
  unfold slashedAt at marked
  cases found : s.validators.data[v.toNat]? with
  | none => simp [found] at marked
  | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

/-- The slashing penalty read at a state only grows along a frame that keeps effective balances. -/
private theorem slashBackAt_le {s t : BeaconState preset fork} (frame : Frame s t)
    (kept : EffectiveKept s t) (v : ValidatorIndex) : slashBackAt s v ≤ slashBackAt t v := by
  unfold slashBackAt
  by_cases marked : slashedAt s v = true
  · rw [ite_eq_left marked, ite_eq_left (slashedAt_of_frame frame marked),
      kept v.toNat (inside_of_slashedAt marked)]
  · rw [ite_eq_right marked]
    exact Nat.zero_le _

/-- A frame that keeps the committee keeps the seats of every old validator. -/
private theorem syncSeats_le {s t : BeaconState preset fork} (frame : Frame s t)
    (altair : .altair ≤ fork)
    (committee : t.currentSyncCommittee altair = s.currentSyncCommittee altair)
    (v : ValidatorIndex) : syncSeats s altair v.toNat ≤ syncSeats t altair v.toNat := by
  unfold syncSeats
  rw [committee]
  cases found : s.validators.data[v.toNat]? with
  | none => simp
  | some w =>
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have keyS : (validatorKeys s)[v.toNat]? = some w.pubkey := by
      simp [validatorKeys, found]
    have keyT : (validatorKeys t)[v.toNat]? = some w.pubkey := by
      obtain ⟨rest, joined⟩ := frame.pubkeysPrefix
      rw [← joined, List.getElem?_append_left (by simpa [validatorKeys] using inside)]
      exact keyS
    cases later : t.validators.data[v.toNat]? with
    | none => simp [validatorKeys, later] at keyT
    | some w' =>
      simp only [validatorKeys, List.getElem?_map, Array.getElem?_toList, later, Option.map_some,
        Option.some.injEq] at keyT
      simp [keyT]

/-- A frame that keeps the committee keeps the sync amount of every old validator. -/
private theorem syncAt_le {s t : BeaconState preset fork} (frame : Frame s t)
    (committee : ∀ altair : .altair ≤ fork,
      t.currentSyncCommittee altair = s.currentSyncCommittee altair)
    (reward : ℕ) (v : ValidatorIndex) : syncAt s reward v ≤ syncAt t reward v := by
  unfold syncAt
  by_cases altair : .altair ≤ fork
  · rw [dite_eq_left altair, dite_eq_left altair]
    exact Nat.mul_le_mul_right _ (syncSeats_le frame altair (committee altair) v)
  · rw [dite_eq_right altair, dite_eq_right altair]

/-- What the blocks of one epoch so far did to the balances, from Fulu.

It is read from the start `a` of the epoch at a later state `s` after `n` blocks. -/
private structure Tally (a s : BeaconState preset fork) (n : ℕ)
    (deb conv props sl : Finset ValidatorIndex) (pc : ValidatorIndex → ℕ)
    (credits shares : ℕ) : Prop where
  within : Within a s
  matched : BalancesMatch s
  persist : ∀ (v : ValidatorIndex) validator, a.validators.data[v.toNat]? = some validator →
    validator.slashed = true → slashedAt s v = true
  debCard : deb.card ≤
    (preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat +
      preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat) *
      n
  convSub : conv ⊆ deb
  down : ∀ v, v ∉ deb → actualBalanceAt ⟨fork, a⟩ v.toNat ≤
    actualBalanceAt ⟨fork, s⟩ v.toNat + slashBackAt s v + n * syncAt s (syncRewardAt a) v
  up : ∀ v, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
    actualBalanceAt ⟨fork, a⟩ v.toNat + n * syncAt s (syncRewardAt a) v + pc v
  converted : ∀ v ∈ conv, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
    preset.MIN_ACTIVATION_BALANCE.toNat + n * syncAt s (syncRewardAt a) v + pc v
  kept : ∀ (v : ValidatorIndex) validator, v ∉ conv →
    a.validators.data[v.toNat]? = some validator →
    ∃ later, s.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator
  pcZero : ∀ v, v ∉ props → pc v = 0
  budget : ∑ v ∈ props, pc v ≤ credits + shares + ∑ v ∈ sl, effectiveAt ⟨fork, s⟩ v.toNat /
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  potential : ∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count →
    Reads a base → (∀ i, a.validators.data.size ≤ i → base i = 0) →
    credits * proposerDenominator + recentFlagSum a altair base count ≤
      recentFlagSum s altair base count
  share : shares ≤ n * (preset.SYNC_COMMITTEE_SIZE.toNat *
    (syncRewardAt a * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)))
  newly : ∀ v ∈ sl, (∀ validator, a.validators.data[v.toNat]? = some validator →
    validator.slashed = false) ∧ slashedAt s v = true
  propsCard : props.card ≤ n
  idle : n = 0 → credits = 0
  propsPos : props.Nonempty → 0 < credits ∨ 0 < shares ∨ sl.Nonempty
  syncRead : 0 < n → SyncRewardRead a
  lives : Lives a s
  life : RegistryLifecycle a s
  persists : SlashedPersistence a s
  eligible : ∀ v ∈ sl, ∃ old, a.validators.data[v.toNat]? = some old ∧
    Eligible (getCurrentEpoch a) old

/-- Before any block, the tally is empty. -/
private theorem Tally.start (a : BeaconState preset fork) (matched : BalancesMatch a) :
    Tally a a 0 ∅ ∅ ∅ ∅ 0 0 0 where
  within := Within.refl a
  matched := matched
  persist v validator found flag := by simp [slashedAt, found, flag]
  debCard := by simp
  convSub := Finset.empty_subset _
  down v _ := by simp
  up v := by simp
  converted v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := ⟨validator, found, rfl⟩
  pcZero _ _ := rfl
  budget := by simp
  potential _ _ _ _ _ _ := by simp
  share := by simp
  newly v member := absurd member (Finset.notMem_empty v)
  propsCard := by simp
  idle _ := rfl
  propsPos h := absurd h (by simp)
  syncRead h := absurd h (Nat.lt_irrefl 0)
  lives := Lives.refl a
  life := .refl a
  persists := .refl a
  eligible v member := absurd member (Finset.notMem_empty v)

/-- A slot step inside the epoch keeps the tally. -/
private theorem Tally.slot {a s cached : BeaconState preset fork} {next : Slot} {n : ℕ}
    {deb conv props sl : Finset ValidatorIndex} {pc : ValidatorIndex → ℕ}
    {credits shares : ℕ} (tally : Tally a s n deb conv props sl pc credits shares)
    (computed : processSlot s = .ok cached)
    (epoch : getCurrentEpoch ({ cached with slot := next } : BeaconState preset fork) =
      getCurrentEpoch s) :
    Tally a { cached with slot := next } n deb conv props sl pc credits shares := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact { tally with
    within := { tally.within with epoch := epoch.trans tally.within.epoch
                                  active := tally.within.active }
    lives := tally.lives.of_data_right rfl
    life := tally.life.trans (.of_data rfl)
    persists := tally.persists.trans (.of_data rfl) }

/-- A block from Fulu extends the tally by one block. -/
private theorem Tally.block {a s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {n : ℕ} {deb conv props sl : Finset ValidatorIndex}
    {pc : ValidatorIndex → ℕ} {credits shares : ℕ}
    (tally : Tally a s n deb conv props sl pc credits shares)
    (fulu : .fusaka ≤ fork)
    (computed : processBlock config checks engine s block = .ok t) :
    ∃ (deb' conv' props' sl' : Finset ValidatorIndex) (pc' : ValidatorIndex → ℕ)
      (credits' shares' : ℕ), Tally a t (n + 1) deb' conv' props' sl' pc' credits' shares' := by
  obtain ⟨paid, cv, slashed, sync, other, slash, proposer, credit, share, ledger,
    paidCard, convCard, credited, penalized, newly, rewards, syncRead, potential, livesB, lifeB,
    eligibleB⟩ := block_balances fulu tally.matched computed
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have frame := frame_processBlock computed
  have steady : Steady s t := ⟨stepKeeps_processBlock computed, effectiveKept_processBlock computed⟩
  have within := tally.within.steady steady
  have committee : ∀ altair : .altair ≤ fork,
      t.currentSyncCommittee altair = s.currentSyncCommittee altair :=
    fun altair => processBlock_currentSyncCommittee altair computed
  have syncMono : ∀ v, syncAt s (syncRewardAt a) v ≤ syncAt t (syncRewardAt a) v :=
    syncAt_le frame committee _
  have backMono : ∀ v, slashBackAt s v ≤ slashBackAt t v := slashBackAt_le frame steady.effective
  -- The participant reward of the block is the one read at the start.
  have rewardEq : syncRewardAt s = syncRewardAt a := by
    unfold syncRewardAt
    rw [tally.within.activeBalanceTotal]
  obtain ⟨seats, shareBound⟩ := rewards altair
  rw [rewardEq] at seats shareBound
  have syncLe : ∀ v, sync v ≤ syncAt t (syncRewardAt a) v := by
    intro v
    unfold syncAt
    rw [dite_eq_left altair]
    exact seats v
  -- The unslashed validators that the block slashes.
  have unslashedS : ∀ v ∈ slashed, slashedAt s v = false := by
    intro v member
    unfold slashedAt
    cases found : s.validators.data[v.toNat]? with
    | none => rfl
    | some w => simp [(newly v member).1 w found]
  have slashedT : ∀ v ∈ slashed, slashedAt t v = true := by
    intro v member
    obtain ⟨later, found, marked⟩ := (newly v member).2
    simp [slashedAt, found, marked]
  have slashLe : ∀ v, slash v + slashBackAt s v ≤ slashBackAt t v := by
    intro v
    have pen := penalized v
    by_cases member : v ∈ slashed
    · rw [ite_eq_left member] at pen
      simp only [slashBackAt, unslashedS v member, slashedT v member, Bool.false_eq_true,
        ↓reduceIte]
      omega
    · rw [ite_eq_right member] at pen
      have := backMono v
      omega
  set whistle := ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with whistleEq
  refine ⟨deb ∪ (paid ∪ cv), conv ∪ cv,
    if 0 < credit + share + whistle then insert proposer props else props,
    sl ∪ slashed, fun v => pc v + other v, credits + credit, shares + share,
    { within := within
      matched := frame.balancesMatch tally.matched
      persist := fun v validator found flag =>
        slashedAt_of_frame frame (tally.persist v validator found flag)
      debCard := ?_
      convSub := Finset.union_subset_union tally.convSub Finset.subset_union_right
      down := ?_
      up := ?_
      converted := ?_
      kept := ?_
      pcZero := ?_
      budget := ?_
      potential := ?_
      share := ?_
      newly := ?_
      propsCard := ?_
      idle := fun h => absurd h (Nat.succ_ne_zero n)
      propsPos := ?_
      syncRead := fun _ => tally.within.read.mp syncRead
      lives := tally.lives.trans livesB tally.life (.of_frame frame)
      life := tally.life.trans lifeB
      persists := tally.persists.trans (.of_frame frame)
      eligible := ?_ }⟩
  · have one := Finset.card_union_le deb (paid ∪ cv)
    have two := Finset.card_union_le paid cv
    have three := tally.debCard
    rw [Nat.mul_succ]
    omega
  · intro v notIn
    simp only [Finset.mem_union, not_or] at notIn
    have h1 := tally.down v notIn.1
    have h2 := ledger.down v notIn.2.1 notIn.2.2
    have h3 := slashLe v
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    omega
  · intro v
    have h1 := tally.up v
    have h2 := ledger.up v
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    omega
  · intro v member
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    by_cases fresh : v ∈ cv
    · have := ledger.converted v fresh
      omega
    · have old : v ∈ conv := by
        rcases Finset.mem_union.mp member with h | h
        · exact h
        · exact absurd h fresh
      have h1 := tally.converted v old
      have h2 := ledger.up v
      omega
  · intro v validator notIn found
    simp only [Finset.mem_union, not_or] at notIn
    obtain ⟨middle, middleFound, same⟩ := tally.kept v validator notIn.1 found
    obtain ⟨later, laterFound, same'⟩ := ledger.kept v middle notIn.2 middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  · intro v notIn
    have notProps : v ∉ props := fun h => notIn (by split <;> simp [h])
    rw [tally.pcZero v notProps, Nat.zero_add]
    have bound := credited v
    split at bound
    · rename_i eq
      subst eq
      have zero : ¬ 0 < credit + share + whistle := fun pos => notIn (by simp [pos])
      omega
    · omega
  · -- The budget: the old credits, and the amount of this block, which goes to its proposer.
    rw [Finset.sum_add_distrib]
    have sub : props ⊆ if 0 < credit + share + whistle then insert proposer props else props := by
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
    rw [← Finset.sum_subset sub fun v _ notIn => tally.pcZero v notIn]
    have blockPart : ∑ v ∈ (if 0 < credit + share + whistle then insert proposer props else props),
        other v ≤ credit + share + whistle := by
      calc _ ≤ ∑ v ∈ (if 0 < credit + share + whistle then insert proposer props else props),
            (if v = proposer then credit + share + whistle else 0) :=
            Finset.sum_le_sum fun v _ => credited v
        _ ≤ credit + share + whistle := by
            rw [Finset.sum_ite_eq']
            split_ifs <;> omega
    have disjoint : Disjoint sl slashed := by
      rw [Finset.disjoint_left]
      intro v inOld inNew
      have := (tally.newly v inOld).2
      rw [unslashedS v inNew] at this
      cases this
    rw [Finset.sum_union disjoint]
    have oldSame : ∑ v ∈ sl, effectiveAt ⟨fork, t⟩ v.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ v ∈ sl, effectiveAt ⟨fork, s⟩ v.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun v member => by
        rw [steady.effective v.toNat (inside_of_slashedAt (tally.newly v member).2)]
    rw [oldSame, ← whistleEq]
    have := tally.budget
    omega
  · intro altair base count big reads support
    have readsS : Reads s base := tally.within.reads reads
    have first := tally.potential altair base count big reads support
    have second := potential altair base count big readsS fun i outside =>
      support i (Nat.le_trans tally.within.size outside)
    rw [Nat.add_mul]
    omega
  · have := tally.share
    rw [Nat.succ_mul]
    omega
  · intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact ⟨(tally.newly v old).1, slashedAt_of_frame frame (tally.newly v old).2⟩
    · refine ⟨fun validator found => ?_, slashedT v fresh⟩
      cases flag : validator.slashed
      · rfl
      · have := tally.persist v validator found flag
        rw [unslashedS v fresh] at this
        cases this
  · split
    · have := Finset.card_insert_le proposer props
      have := tally.propsCard
      omega
    · have := tally.propsCard
      omega
  · intro nonempty
    split at nonempty
    · rename_i positive
      by_cases c : 0 < credit
      · left; omega
      by_cases d : 0 < share
      · right; left; omega
      right; right
      have : 0 < whistle := by omega
      obtain ⟨v, member⟩ : slashed.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro empty
        rw [whistleEq, empty, Finset.sum_empty] at this
        exact Nat.lt_irrefl 0 this
      exact ⟨v, Finset.mem_union_right _ member⟩
    · rcases tally.propsPos nonempty with h | h | ⟨v, member⟩
      · left; omega
      · right; left; omega
      · right; right; exact ⟨v, Finset.mem_union_left _ member⟩
  · intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact tally.eligible v old
    · obtain ⟨w, found, eligible⟩ := eligibleB v fresh
      rw [tally.within.epoch] at eligible
      exact tally.lives.back tally.life tally.persists found eligible

/-- The flag potential is at most `108` times the sum of the weights it reads. -/
private theorem recentFlagSum_le (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (base : ℕ → ℕ) (count : ℕ) :
    recentFlagSum s altair base count ≤ 108 * ∑ i ∈ Finset.range count, base i := by
  have one := flagSumOf_le base count (s.previousEpochParticipation altair)
  have two := flagSumOf_le base count (s.currentEpochParticipation altair)
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]
  unfold recentFlagSum
  omega

end Epoch

/-- The tally of a run inside one epoch, from Fulu, read at its last state. -/
private theorem Run.tally {F : Fork} {a : BeaconState preset F} {y : ForkedBeaconState preset}
    (tail : Run config checks ⟨F, a⟩ y)
    (same : getCurrentEpoch y.state = getCurrentEpoch a) (matched : BalancesMatch a) :
    ∃ b : BeaconState preset F, y = ⟨F, b⟩ ∧
      (.fusaka ≤ F → ∃ (deb conv props sl : Finset ValidatorIndex) (pc : ValidatorIndex → ℕ)
        (credits shares : ℕ), Tally a b tail.blockCount deb conv props sl pc credits shares) :=
    Run.induction_of_same_epoch (fun z pre => ∃ s : BeaconState preset F, z = ⟨F, s⟩ ∧
      (.fusaka ≤ F → ∃ (deb conv props sl : Finset ValidatorIndex) (pc : ValidatorIndex → ℕ)
        (credits shares : ℕ), Tally a s pre.blockCount deb conv props sl pc credits shares))
      ⟨a, rfl, fun _ => ⟨_, _, _, _, _, _, _,
        by simpa [Run.blockCount] using Tally.start a matched⟩⟩
      (fun engine signed due ok pre prior => by
        obtain ⟨_, eq, prior⟩ := prior
        cases eq
        refine ⟨_, rfl, fun fulu => ?_⟩
        obtain ⟨_, _, _, _, _, _, _, tally⟩ := prior fulu
        exact tally.block fulu (applySignedBlock_ok ok).2.1)
      (fun pre ok last computed epoch prior => by
        have count : (pre.snoc (.slot ok)).blockCount = pre.blockCount := rfl
        generalize pre.snoc (.slot ok) = run at count ⊢
        clear ok
        obtain ⟨_, rfl, prior⟩ := prior
        subst last
        rw [count]
        exact ⟨_, rfl, fun fulu => by
          obtain ⟨_, _, _, _, _, _, _, tally⟩ := prior fulu
          exact ⟨_, _, _, _, _, _, _, tally.slot computed epoch⟩⟩)
      tail same

/-- Inside one epoch, from Fulu, take each validator with an exit set.

Its withdrawable epoch only rises, and moves only for a slashed validator. -/
theorem Run.withdrawableKept_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (fulu : .fusaka ≤ y.fork)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state) (matched : BalancesMatch x.state) :
    WithdrawableKept x.state y.state := by
  obtain ⟨F, a⟩ := x
  obtain ⟨b, rfl, tallied⟩ := Run.tally tail same matched
  obtain ⟨_, _, _, _, _, _, _, tally⟩ := tallied fulu
  exact tally.lives.withdrawableKept

/-! ## The branch corrections -/

/-- Along a run inside one epoch, from Fulu, balances move by bounded amounts.

The bounds are read at the last state of the run. -/
theorem Run.balanceCorrections_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (fulu : .fusaka ≤ y.fork)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    -- The exits of the first state must be ordered.
    (matched : BalancesMatch x.state) (exits : ExitsOrdered x.state) :
    let state := y.state
    let slots := preset.SLOTS_PER_EPOCH.toNat
    let p := parameters preset y.fork
    let positions := Finset.range state.validators.data.size
    let validator (i : ℕ) := state.validators.data[i]?
    let effective (i : ℕ) := balanceAt state i
    let current (i : ℕ) := isActiveAt state (getCurrentEpoch state) i
    let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
    let recent (i : ℕ) := before i || current i
    let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
    let totalGwei := (getTotalActiveBalance state).toOption.getD 0
    let base (i : ℕ) := ((getBaseReward state totalGwei (UInt64.ofNat i)).toOption.getD 0).toNat
    let seatReward := if .altair ≤ y.fork then ((syncParticipantReward state).toOption.getD 0).toNat
      else 0
    let seats (i : ℕ) := if altair : .altair ≤ y.fork then syncSeats state altair i else 0
    let sync (i : ℕ) := seats i * seatReward
    let syncProposer := if .altair ≤ y.fork then
        slots * preset.SYNC_COMMITTEE_SIZE.toNat *
          ((syncProposerReward (UInt64.ofNat seatReward)).toOption.getD 0).toNat
      else 0
    let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
    let whistleblowerP :=
      (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
    let slashBack (i : ℕ) :=
      if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
    let blocks := tail.blockCount
    let debited := ((if .shapella ≤ y.fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
      (if .pectra ≤ y.fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) *
        blocks
    let blockDeposits := if h : y.fork < .hegota then
        (if .pectra ≤ y.fork then 0
         else min (preset.MAX_DEPOSITS.toNat * blocks) (state.eth1DepositIndex h).toNat)
      else 0
    let creditedP :=
      (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0
        else blocks) + blockDeposits
    ∃ (debitedKeys creditedKeys : Finset ValidatorIndex) (pc deposit : ValidatorIndex → ℕ),
      -- A withdrawal or a conversion debits a validator, at most the payload limits per block.
      debitedKeys.card ≤ debited ∧ creditedKeys.card ≤ creditedP ∧
      -- Off the debited validators, a balance falls by at most its slashing and sync penalties.
      (∀ v, v ∉ debitedKeys → actualBalanceAt x v.toNat ≤
        actualBalanceAt y v.toNat + slashBack v.toNat + blocks * sync v.toNat) ∧
      -- A balance rises by at most the sync rewards of the blocks and its other credits.
      (∀ v, actualBalanceAt y v.toNat ≤
        actualBalanceAt x v.toNat + blocks * sync v.toNat + pc v + deposit v) ∧
      -- The other credits are zero off the credited validators.
      (∀ v, v ∉ creditedKeys → pc v = 0 ∧ deposit v = 0) ∧
      -- From Electra, a block credits no deposit to a balance.
      (.pectra ≤ y.fork → ∀ v, deposit v = 0) ∧
      -- Credits apart from deposits sum to at most the proposer credit and whistleblower rewards.
      --
      -- The proposer credit covers attestation rewards and the proposer share of sync aggregates.
      --
      -- The whistleblower rewards are those of the validators slashed at the last state.
      ∑ v ∈ creditedKeys, pc v ≤ proposerCredit + whistleblowerP ∧
      -- The bound also holds with only the validators slashed within the run.
      (∃ slashedNow : Finset ValidatorIndex,
        -- Those validators were slashable at the first state.
        (∀ v ∈ slashedNow, (∀ validator, x.state.validators.data[v.toNat]? = some validator →
            validator.slashed = false) ∧ slashed v.toNat = true ∧
          ∃ validator, x.state.validators.data[v.toNat]? = some validator ∧
            validator.activationEpoch ≤ getCurrentEpoch x.state ∧
            getCurrentEpoch x.state < validator.withdrawableEpoch) ∧
        ∑ v ∈ creditedKeys, pc v ≤ (∑ i ∈ positions with recent i, base i) + syncProposer +
          (∑ v ∈ slashedNow, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ∧
      -- A validator whose largest effective balance changed was converted.
      --
      -- A converted balance ends within the activation balance above its later credits.
      (∀ v validator later, x.state.validators.data[v.toNat]? = some validator →
        y.state.validators.data[v.toNat]? = some later →
        withdrawalMaxEffectiveBalance preset y.fork later ≠
          withdrawalMaxEffectiveBalance preset x.fork validator →
        actualBalanceAt y v.toNat ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
          blocks * sync v.toNat + pc v + deposit v) ∧
      -- The credited validators are the proposers and the deposit recipients.
      (∃ proposerKeys depositKeys : Finset ValidatorIndex,
        creditedKeys = proposerKeys ∪ depositKeys ∧
        proposerKeys.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
          positions.filter (slashed ·) = ∅ then 0 else blocks) ∧
        depositKeys.card ≤ blockDeposits ∧
        (∀ v, v ∉ proposerKeys → pc v = 0) ∧ (∀ v, v ∉ depositKeys → deposit v = 0)) ∧
      -- Off the debited validators, the largest effective balance stays.
      (∀ v validator, v ∉ debitedKeys → x.state.validators.data[v.toNat]? = some validator →
        ∃ later, y.state.validators.data[v.toNat]? = some later ∧
          withdrawalMaxEffectiveBalance preset y.fork later =
            withdrawalMaxEffectiveBalance preset x.fork validator) ∧
      -- Effective balances stay.
      x.fork = y.fork ∧ EffectiveKept x.state y.state := by
  obtain ⟨F, a⟩ := x
  obtain ⟨b, rfl, tallied⟩ := Run.tally tail same matched
  obtain ⟨deb, conv, props, sl, pc, credits, shares, tally⟩ := tallied fulu
  intro state slots p positions validator effective current before recent slashed totalGwei
    base seatReward seats sync syncProposer proposerCredit whistleblowerP slashBack
    blocks debited blockDeposits creditedP
  have altair : .altair ≤ F := Nat.le_trans (by decide) fulu
  have capella : .shapella ≤ F := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ F := Nat.le_trans (by decide) fulu
  -- With a block, the sync step read the participant reward, its total and its proposer share.
  --
  -- So the last state reads them too.
  have read : 0 < blocks → ∃ (reward total share : Gwei),
      syncParticipantReward b = .ok reward ∧ reward.toNat = syncRewardAt a ∧
      getTotalActiveBalance b = .ok total ∧ total.toNat = activeBalanceTotal b ∧
      syncProposerReward reward = .ok share ∧ share.toNat = reward.toNat *
        PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) := by
    intro positive
    obtain ⟨reward, rewardOk⟩ := tally.within.read.mpr (tally.syncRead positive)
    obtain ⟨total, -, totalOk, -, -, -⟩ := syncParticipantReward_ok rewardOk
    obtain ⟨share, shareOk, shareValue⟩ := syncProposerReward_of_participant rewardOk
    refine ⟨reward, total, share, rewardOk, ?_, totalOk, getTotalActiveBalance_toNat totalOk,
      shareOk, shareValue⟩
    rw [(syncRewardRead_of_ok rewardOk).1]
    unfold syncRewardAt
    rw [tally.within.activeBalanceTotal]
  -- The participant reward read at the start is the reward read at the end.
  have rewardEq : 0 < blocks → syncRewardAt a = seatReward := by
    intro positive
    obtain ⟨reward, -, -, rewardOk, rewardValue, -⟩ := read positive
    simp only [seatReward, state, ite_eq_left altair, rewardOk, Except.toOption, Option.getD_some,
      rewardValue]
  have syncEq : ∀ v, blocks * syncAt b (syncRewardAt a) v = blocks * sync v.toNat := by
    intro v
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · rw [zero, Nat.zero_mul, Nat.zero_mul]
    · rw [rewardEq positive]
      simp only [syncAt, dite_eq_left altair, sync, seats]
      rfl
  -- The proposer credits of attestations are at most the base rewards of the recent validators.
  have creditsLe : credits ≤ ∑ i ∈ positions with recent i, base i := by
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · rw [tally.idle zero]; exact Nat.zero_le _
    obtain ⟨-, total, -, -, -, totalOk, totalValue, -⟩ := read positive
    let weight (i : ℕ) := if recent i then base i else 0
    have readsB : Reads b weight := by
      intro index tot reward recentB totValue rewardOk
      have isRecent : recent index.toNat = true := by
        simp only [recent, before, current, Bool.or_eq_true]; exact recentB
      -- The read total is the total of the last state.
      obtain rfl : tot = total := UInt64.toNat_inj.mp (totValue.trans totalValue.symm)
      rw [show weight index.toNat = base index.toNat from ite_eq_left isRecent]
      simp only [base, totalGwei, state, totalOk, rewardOk, Except.toOption, Option.getD_some,
        UInt64.ofNat_toNat]
    have support : ∀ i, a.validators.data.size ≤ i → weight i = 0 := by
      intro i outside
      by_cases isRecent : recent i = true
      · have recentB : isActiveAt b (getPreviousEpoch b) i = true ∨
            isActiveAt b (getCurrentEpoch b) i = true := by
          simpa [recent, before, current] using isRecent
        have := lt_size_of_isActiveAt_recent ((tally.within.recent i).mp recentB)
        omega
      · exact ite_eq_right isRecent
    -- The potential counts every position of the registry, however large it is.
    let count := max (2 ^ 64) b.validators.data.size
    have bound := tally.potential altair weight count (Nat.le_max_left _ _)
      (tally.within.reads_back readsB) support
    have upper := recentFlagSum_le b altair weight count
    have sumEq : ∑ i ∈ Finset.range count, weight i =
        ∑ i ∈ positions with recent i, base i := by
      rw [show ∑ i ∈ Finset.range count, weight i =
        ∑ i ∈ Finset.range count, (if recent i = true then base i else 0) from rfl,
        ← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro i member
        simp only [Finset.mem_filter, Finset.mem_range, positions] at member ⊢
        exact ⟨Nat.lt_of_lt_of_le member.1 (Nat.le_max_right _ _), member.2⟩
      · intro i member notIn
        exfalso
        simp only [Finset.mem_filter, Finset.mem_range, positions, not_and] at member notIn
        have recentB : isActiveAt b (getPreviousEpoch b) i = true ∨
            isActiveAt b (getCurrentEpoch b) i = true := by
          simpa [recent, before, current] using member.2
        exact notIn (lt_size_of_isActiveAt_recent recentB) member.2
    have denominator : proposerDenominator = 448 := by decide
    rw [denominator] at bound
    rw [sumEq] at upper
    omega
  -- A run inside one epoch has at most one block for each slot of the epoch.
  have blocksLe : 0 < slots → blocks ≤ slots := by
    intro positive
    simpa only [blocks, same, Nat.add_sub_cancel_left, Nat.one_mul] using
      tail.blockCount_le_epochs positive
  -- The proposer shares of the sync aggregates.
  have sharesLe : shares ≤ syncProposer := by
    have bound := tally.share
    change shares ≤ blocks * _ at bound
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · rw [zero, Nat.zero_mul] at bound
      omega
    obtain ⟨reward, -, share, rewardOk, rewardValue, -, -, shareOk, shareValue⟩ := read positive
    have proposerEq : syncProposer = slots * preset.SYNC_COMMITTEE_SIZE.toNat * share.toNat := by
      simp only [syncProposer, ite_eq_left altair, seatReward, state, rewardOk, Except.toOption,
        Option.getD_some, UInt64.ofNat_toNat, shareOk]
    rw [proposerEq, shareValue, rewardValue]
    rcases Nat.eq_zero_or_pos slots with none | some
    · have : syncRewardAt a = 0 := by
        simp only [syncRewardAt, show preset.SLOTS_PER_EPOCH.toNat = 0 from none, Nat.div_zero,
          Nat.zero_div]
      rw [this, Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.mul_zero] at bound
      omega
    · calc shares ≤ blocks * _ := bound
        _ ≤ slots * _ := Nat.mul_le_mul_right _ (blocksLe some)
        _ = _ := by rw [Nat.mul_assoc]
  have whistleLe : ∑ v ∈ sl, effectiveAt ⟨F, b⟩ v.toNat /
      (parameters preset F).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (∑ v ∈ sl, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    have quotients := Base.sum_map_div_le (fun v => effectiveAt ⟨F, b⟩ v.toNat)
      p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat sl.toList
    simp only [Finset.sum_map_toList] at quotients
    exact quotients
  have slashedSub : ∑ v ∈ sl, effective v.toNat ≤ ∑ i ∈ positions with slashed i, effective i := by
    rw [← Finset.sum_image (f := effective) (s := sl) (g := UInt64.toNat)
      (fun x _ y _ eq => UInt64.toNat_inj.mp eq)]
    apply Finset.sum_le_sum_of_subset
    intro i member
    obtain ⟨v, inSl, rfl⟩ := Finset.mem_image.mp member
    have marked := (tally.newly v inSl).2
    simp only [Finset.mem_filter, Finset.mem_range, positions]
    exact ⟨inside_of_slashedAt marked, marked⟩
  have budget : ∑ v ∈ props, pc v ≤ (∑ i ∈ positions with recent i, base i) +
      syncProposer + (∑ v ∈ sl, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    have := tally.budget
    omega
  -- The credited validators.
  have propsCard : props.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
      positions.filter (slashed ·) = ∅ then 0 else blocks) := by
    split
    · rename_i zero
      obtain ⟨credit0, -, slash0⟩ := zero
      have credit0' : (∑ i ∈ positions with recent i, base i) + syncProposer = 0 := credit0
      suffices empty : props = ∅ by rw [empty]; rfl
      by_contra nonempty
      rcases tally.propsPos (Finset.nonempty_iff_ne_empty.mpr nonempty) with
        positive | positive | ⟨v, member⟩
      · omega
      · omega
      · have marked := (tally.newly v member).2
        have : v.toNat ∈ positions.filter (slashed ·) := by
          simp only [Finset.mem_filter, Finset.mem_range, positions]
          exact ⟨inside_of_slashedAt marked, marked⟩
        rw [slash0] at this
        exact Finset.notMem_empty _ this
    · exact tally.propsCard
  refine ⟨deb, props, pc, fun _ => 0, ?_, Nat.le_trans propsCard (Nat.le_add_right _ _), ?_, ?_,
    fun v notIn => ⟨tally.pcZero v notIn, rfl⟩, fun _ _ => rfl,
    Nat.le_trans budget (Nat.add_le_add_left (Nat.div_le_div_right slashedSub) _), ?_, ?_,
    ⟨props, ∅, (Finset.union_empty props).symm, propsCard, by simp, tally.pcZero,
      fun _ _ => rfl⟩, ?_, rfl, tally.within.effective⟩
  · simpa only [debited, capella, electra, ↓reduceIte] using tally.debCard
  · intro v notIn
    have := tally.down v notIn
    rw [syncEq v] at this
    exact this
  · intro v
    have := tally.up v
    rw [syncEq v] at this
    exact this
  · refine ⟨sl, fun v member => ⟨(tally.newly v member).1, (tally.newly v member).2, ?_⟩,
      budget⟩
    obtain ⟨old, found, -, active, below, window⟩ := tally.eligible v member
    refine ⟨old, found, active, ?_⟩
    rcases window with far | before
    · have ordered := exits old (Array.mem_of_getElem? found)
      rw [far] at ordered
      exact UInt64.lt_of_lt_of_le below ordered
    · exact before
  · intro v validator later found foundB differ
    have member : v ∈ conv := by
      by_contra notConv
      obtain ⟨later', found', same⟩ := tally.kept v validator notConv found
      have : some later' = some later := found'.symm.trans foundB
      cases this
      apply differ
      simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, same]
    have := tally.converted v member
    rw [syncEq v] at this
    exact this
  · intro v validator notIn found
    obtain ⟨later, foundB, same⟩ := tally.kept v validator (fun h => notIn (tally.convSub h)) found
    exact ⟨later, foundB,
      by simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, same]⟩

end EthLib.Consensus
