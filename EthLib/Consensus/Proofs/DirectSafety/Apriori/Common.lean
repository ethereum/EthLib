module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Reserved.Epoch

import EthLib.Serialization.Proofs.Ssz.Merkle.MultiproofPositions

/-!
# The common ledger

The stake that two branches from the reference state share, before and after Electra.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-- Conditional composition needs the derived envelope and the ledger at cached calls.

It does not need the resource and per-key producers that establish them.

The cached-call ledger remains an explicit input.

The ledger of the common slashed stake is stated on run endpoints.

But the two selected calls observe cached states inside epoch processing. -/
theorem composition_conditional_of_call_ledger
    (derived : ∀ g x y : ForkedBeaconState preset,
      DerivedProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (identities : ∀ x y c, ReducedIdentity (preset := preset) x y c)
    (callLedger : ∀ {g x a b : ForkedBeaconState preset}
      (shared : Run config checks g x) (left : Run config checks x a)
      (right : Run config checks x b), Parameters preset →
      Genesis (config := config) (checks := checks) g → CapOrder preset →
      MaxEffectiveBalancesAligned preset → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
      a.fork < .glamsterdam → b.fork < .glamsterdam → ∀ high,
      aprioriGuardAt config x high → ∀ low,
      x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat →
      ∀ one two : EitherCall (shared.append left) (shared.append right),
      low ≤ one.targetEpoch → one.targetEpoch ≤ high →
      low ≤ two.targetEpoch → two.targetEpoch ≤ high →
      let c := exitedBefore x (min one.targetEpoch two.targetEpoch)
      c ∩ recentKeys one.state.state = ∅ → c ∩ recentKeys two.state.state = ∅ →
      stateDrift x one.state + 2 * commonSlashed x one.state c ≤ drift (config := config) x high ∧
      stateDrift x two.state + 2 * commonSlashed x two.state c ≤ drift (config := config) x high)
    (absence : CachedAbsenceProducer (preset := preset) (config := config) (checks := checks))
    (transfer : ReducedTransferProducer (preset := preset) (config := config) (checks := checks)) :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) := by
  have subset (x : ForkedBeaconState preset) (cutoff : Nat) :
      exitedBefore x cutoff ⊆ unslashedKeys x.state := by
    unfold exitedBefore
    split
    · simp
    · exact Finset.filter_subset _ _
  have fallback (x : ForkedBeaconState preset) (high : Nat)
      (guard : ¬ aprioriGuardAt config x high) :
      Models.stake (effectiveWeight x.state) (unslashedKeys x.state) =
        drift (config := config) x high := by
    have bounded := Models.stake_mono (w := effectiveWeight x.state)
      (Finset.filter_subset (¬ SlashedAt x.state ·) (activeKeys x.state))
    change Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
      Models.stake (effectiveWeight x.state) (activeKeys x.state) at bounded
    simp only [drift, ite_eq_right guard, slashedActiveStake]
    unfold referenceStake at *
    omega
  refine ⟨?_, ?_⟩
  · intro g x a b shared left right parameters genesis _delay twoSlots caps aligned
      earlyA earlyB start enoughA enoughB ordered conflict
    by_cases guard : aprioriGuardAt config x b.state.finalizedCheckpoint.epoch.toNat
    · have first := derived g x a shared left genesis parameters caps aligned twoSlots earlyA _
        start guard
      have second := derived g x b shared right genesis parameters caps aligned twoSlots earlyB _
        start guard
      rcases accountable_safety shared left right parameters genesis enoughA enoughB ordered
        conflict with bound | hashes
      · exact .inl (bound.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_left 2 (max_le first second)) _))
      · exact .inr hashes
    · have small := fallback x _ guard
      exact .inl (by omega)
  · intro g x a b shared left right parameters genesis caps aligned _delay twoSlots
      earlyA earlyB _start enoughA enoughB ordered conflict guard
    rcases transfer shared left right parameters genesis enoughA enoughB ordered conflict with
      ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, bound⟩ | hashes
    · refine .inl ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, ?_⟩
      let cutoff := min one.targetEpoch two.targetEpoch
      let c := exitedBefore x cutoff
      have inside : c ⊆ unslashedKeys x.state := subset x cutoff
      have missing : c ∩ recentKeys one.state.state = ∅ ∧
          c ∩ recentKeys two.state.state = ∅ := by
        by_cases later : (getCurrentEpoch x.state).toNat < cutoff
        · exact absence shared left right genesis parameters one two later
        · have empty : c = ∅ := by simp [c, exitedBefore, cutoff, Nat.le_of_not_gt later]
          simp [empty]
      have ledger := callLedger shared left right parameters genesis caps aligned twoSlots
        earlyA earlyB _ guard _ (conflict_starts shared left right _ _ ordered conflict)
        one two lowerOne upperOne lowerTwo upperTwo missing.1 missing.2
      have first := identities x one.state c inside missing.1
      have second := identities x two.state c inside missing.2
      have partition := Models.stake_add_stake_sdiff (w := effectiveWeight x.state) c
        (unslashedKeys x.state)
      have empty : c \ unslashedKeys x.state = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr inside
      rw [empty, Models.stake_empty, Nat.add_zero] at partition
      have accountable := Models.stake_mono (w := effectiveWeight x.state)
        (Finset.sdiff_subset : accountableKeys shared left right \ c ⊆ accountableKeys shared left
              right)
      change Models.stake (effectiveWeight x.state) (unslashedKeys x.state \ c) ≤
        3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right \ c) +
        reducedDrift x one.state c + reducedDrift x two.state c at bound
      change stateDrift x one.state + 2 * commonSlashed x one.state c ≤
          drift (config := config) x b.state.finalizedCheckpoint.epoch.toNat ∧
        stateDrift x two.state + 2 * commonSlashed x two.state c ≤
          drift (config := config) x b.state.finalizedCheckpoint.epoch.toNat at ledger
      change Models.stake (effectiveWeight x.state) (unslashedKeys x.state) +
        3 * Models.stake (effectiveWeight x.state) c ≤ _
      omega
    · exact .inr hashes

/-- An endpoint ledger transports to the cached state of a call in the tail. -/
theorem selected_call_commonLedger {g x y : ForkedBeaconState preset}
    (ledger : ∀ z : ForkedBeaconState preset,
      CommonLedger (config := config) (checks := checks) (g := g) (x := x) (y := z))
    (shared : Run config checks g x) (tail : Run config checks x y)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .glamsterdam)
    (high low : Nat) (guard : aprioriGuardAt config x high)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail))
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high)
    (cutoff : Nat) (cutoffLe : cutoff ≤ high + 1)
    (absent : exitedBefore x cutoff ∩ recentKeys call.cached = ∅) :
    stateDrift x ⟨call.before.fork, call.cached⟩ +
      2 * commonSlashed x ⟨call.before.fork, call.cached⟩ (exitedBefore x cutoff) ≤
        drift (config := config) x high := by
  have member := call_after_reference shared tail parameters low starts call lower
  obtain ⟨pre, _, _, beforeEarly, _⟩ := Run.contains_step_facts member early
  have cached := call.cached_frame x
  have bounded : (getCurrentEpoch call.before.state).toNat ≤ high + 1 := by
    have target := call.currentEpoch_le
    rw [cached.1] at target
    omega
  have support : Supported shared pre high :=
    ⟨genesis, parameters, caps, aligned, beforeEarly, bounded, guard⟩
  rw [cached.2.2.1] at absent
  have read := ledger call.before shared pre high support twoSlots cutoff absent cutoffLe
  simpa only [cached.2.2.2, commonSlashed, cached.2.1] using read

/-- A successful checked active-index read identifies the validator behind every selected key. -/
private theorem cached_active_member {fork : Fork} {s : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex}
    (checked : getActiveValidatorIndicesChecked s epoch = .ok indices)
    {key : Cryptography.Bls.BLSPubkey}
    (member : key ∈ keysAt s (getActiveValidatorIndices s epoch)) :
    ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
      isActiveValidator v epoch = true := by
  simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨i, active, found⟩ := member
  rw [← getActiveValidatorIndicesChecked_ok checked] at active
  obtain ⟨v, read, active⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp active
  exact ⟨i.toNat, v, read, by simpa [read] using found, active⟩

/-- Assigned exits before the selected cutoff cannot reappear in a call's recent support. -/
private theorem selected_call_absence {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (call : QuorumCall (shared.append tail))
    (cutoff : Nat) (later : (getCurrentEpoch x.state).toNat < cutoff)
    (lower : cutoff ≤ call.target.epoch.toNat) :
    exitedBefore x cutoff ∩ recentKeys call.cached = ∅ := by
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := parameters.slots
  have starts : x.state.slot.toNat ≤ cutoff * preset.SLOTS_PER_EPOCH.toNat := by
    apply Nat.le_of_lt ((Nat.div_lt_iff_lt_mul positive).mp ?_)
    simpa only [getCurrentEpoch_toNat] using later
  obtain ⟨pre, _, _⟩ := tail.contains_split (.slot call.advanced)
    (call_after_reference shared tail parameters cutoff starts call lower)
  obtain ⟨_, _, _, _, validators, _⟩ := call.toEpochCall.selected_prefix
  have unique := call.toEpochCall.pubkeysDistinct genesis
  have epochLower : cutoff ≤ (getCurrentEpoch call.cached).toNat := by
    have target := call.targetEpoch
    cases current : call.current <;>
      simp only [current, Bool.false_eq_true, ↓reduceIte] at target <;>
      rw [target] at lower
    · have previous := getPreviousEpoch_toNat call.cached
      omega
    · exact lower
  have previousRead : ∃ indices,
      getActiveValidatorIndicesChecked call.cached (getPreviousEpoch call.cached) =
          .ok indices := by
    by_cases early : call.before.fork < .altair
    · exact ⟨_, getActiveValidatorIndicesChecked_of_within
        (call.cached.validators.bound (Nat.lt_trans early (by decide))) _⟩
    · rcases processJustificationAndFinalization_reads call.weighedOk with small | reads
      · exact False.elim ((Nat.not_le_of_gt call.later) small.1)
      · obtain ⟨_, previous, _, _, _, _, counted, _⟩ := reads
        rcases targetIndices_ok counted with ⟨altair, counted⟩ | ⟨before, _⟩
        · unfold getUnslashedParticipatingIndices at counted
          dsimp only at counted
          split at counted
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at counted
            obtain ⟨indices, checked, _⟩ := counted
            exact ⟨indices, checked⟩
          · contradiction
        · exact False.elim (early before)
  obtain ⟨total, _, _, _, totalOk, _⟩ := call.passes
  obtain ⟨currentIndices, currentRead, _⟩ := bind_ok_iff.mp totalOk
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro key both
  obtain ⟨common, recent⟩ := Finset.mem_inter.mp both
  simp only [exitedBefore, ite_eq_right (Nat.not_le_of_gt later), Finset.mem_filter] at common
  obtain ⟨_, old, member, oldKey, exited⟩ := common
  obtain ⟨i, found⟩ := Array.getElem?_of_mem (by simpa using member)
  have assigned : old.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have upper := call.target.epoch.toNat_lt
    simp only [far, FAR_FUTURE_EPOCH] at exited
    have farNat : (UInt64.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide
    rw [farNat] at exited
    omega
  obtain ⟨v, read, life⟩ := pre.registryLifecycle.validators i old found
  obtain ⟨w, wRead, keySame⟩ := validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps pre.chainSteps).1 found
  have equal : w = v := Option.some.inj (wRead.symm.trans read)
  have keyV : v.pubkey = key := equal ▸ keySame.trans oldKey
  have cachedRead : call.cached.validators.data[i]? = some v := by simpa [validators] using read
  have identify {j : Nat} {z : Validator} (readZ : call.cached.validators.data[j]? = some z)
      (keyZ : z.pubkey = key) : z = v := by
    exact List.inj_on_of_nodup_map unique
      (by simpa using Array.mem_of_getElem? readZ)
      (by simpa using Array.mem_of_getElem? cachedRead) (keyZ.trans keyV.symm)
  have exitSame := congrArg UInt64.toNat (life.exitEpoch assigned)
  have previous := getPreviousEpoch_toNat call.cached
  obtain ⟨recent, _⟩ := Finset.mem_filter.mp recent
  rcases Finset.mem_union.mp recent with active | active
  · obtain ⟨j, z, readZ, keyZ, active⟩ := cached_active_member currentRead active
    have same := identify readZ keyZ
    rw [same] at active
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    omega
  · obtain ⟨indices, checked⟩ := previousRead
    obtain ⟨j, z, readZ, keyZ, active⟩ := cached_active_member checked active
    have same := identify readZ keyZ
    rw [same] at active
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    omega

theorem cachedAbsence_proved :
    CachedAbsenceProducer (preset := preset) (config := config) (checks := checks) := by
  intro g x a b shared left right genesis parameters one two later
  have selected (call : EitherCall (shared.append left) (shared.append right))
      (lower : min one.targetEpoch two.targetEpoch ≤ call.targetEpoch) :
      exitedBefore x (min one.targetEpoch two.targetEpoch) ∩ recentKeys call.state.state = ∅ := by
    cases call with
    | inl call => exact selected_call_absence shared left genesis parameters call _ later lower
    | inr call => exact selected_call_absence shared right genesis parameters call _ later lower
  exact ⟨selected one (Nat.min_le_left _ _), selected two (Nat.min_le_right _ _)⟩

/-- The selected conflicting quorums transfer any reduced unslashed reference through the core. -/
theorem reducedTransfer_proved :
    ReducedTransferProducer (preset := preset) (config := config) (checks := checks) := by
  intro g x a b shared left right parameters genesis enoughA enoughB ordered conflict
  rcases accountable_safety_at_calls_reference shared left right parameters genesis
      b.state.finalizedCheckpoint enoughA enoughB (.inr (.inr rfl)) ordered conflict
      (fun e f => unslashedKeys x.state \ exitedBefore x (min e f))
      (fun _ _ => Finset.sdiff_subset) with
    ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, bound⟩ | hashes
  · let c := exitedBefore x (min one.targetEpoch two.targetEpoch)
    have same : (unslashedKeys x.state \ c).filter (Accountable shared left right) =
        accountableKeys shared left right \ c := by
      ext k
      simp only [accountableKeys, Finset.mem_filter, Finset.mem_sdiff]
      tauto
    dsimp only at bound
    rw [same] at bound
    refine .inl ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, ?_⟩
    exact bound
  · exact .inr hashes

section

open Cryptography.Bls

/-- Take the drift on the unslashed keys outside `c`.

Add twice the stake of `c` still unslashed at `y`.

The sum is the drift on all the unslashed keys.

The keys of `c` are not recent at `y`.

So each of them loses all its effective balance when it is unslashed at `y`, and none gains. -/
theorem reducedIdentity (x y : ForkedBeaconState preset) (c : Finset BLSPubkey) :
    ReducedIdentity (preset := preset) x y c := by
  intro inside apart
  have notRecent : ∀ k ∈ c, k ∉ recentKeys y.state := fun k member recent =>
    (Finset.eq_empty_iff_forall_notMem.mp apart) k (Finset.mem_inter.mpr ⟨member, recent⟩)
  -- A recent key is outside `c`, so it has the same support in both reference sets.
  have gain : (∑ k ∈ recentKeys y.state, (effectiveWeight y.state k -
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k)) =
      ∑ k ∈ recentKeys y.state, (effectiveWeight y.state k -
        Models.supported (unslashedKeys x.state \ c) (effectiveWeight x.state) k) := by
    refine Finset.sum_congr rfl fun k recent => ?_
    have outside : k ∉ c := fun member => notRecent k member recent
    simp only [Models.supported, Finset.mem_sdiff, outside, not_false_eq_true, and_true]
  -- The unslashed keys split into those outside `c` and those of `c`.
  have loss : (∑ k ∈ (unslashedKeys x.state).filter (¬ SlashedAt y.state ·),
        (effectiveWeight x.state k -
          Models.supported (recentKeys y.state) (effectiveWeight y.state) k)) =
      (∑ k ∈ (unslashedKeys x.state \ c).filter (¬ SlashedAt y.state ·),
        (effectiveWeight x.state k -
          Models.supported (recentKeys y.state) (effectiveWeight y.state) k)) +
      Models.stake (effectiveWeight x.state) (c.filter (¬ SlashedAt y.state ·)) := by
    have split : (unslashedKeys x.state).filter (¬ SlashedAt y.state ·) =
        ((unslashedKeys x.state \ c).filter (¬ SlashedAt y.state ·)) ∪
          c.filter (¬ SlashedAt y.state ·) := by
      rw [← Finset.filter_union, Finset.sdiff_union_of_subset inside]
    have disjoint : Disjoint ((unslashedKeys x.state \ c).filter (¬ SlashedAt y.state ·))
        (c.filter (¬ SlashedAt y.state ·)) :=
      Finset.disjoint_filter_filter Finset.sdiff_disjoint
    rw [split, Finset.sum_union disjoint]
    congr 1
    unfold Models.stake
    refine Finset.sum_congr rfl fun k member => ?_
    have outside := notRecent k (Finset.mem_filter.mp member).1
    simp only [Models.supported, outside, ↓reduceIte, Nat.sub_zero]
  -- The stake of `c` is its slashed part and its unslashed part.
  have parts : Models.stake (effectiveWeight x.state) c =
      commonSlashed x y c + Models.stake (effectiveWeight x.state)
        (c.filter (¬ SlashedAt y.state ·)) := by
    unfold commonSlashed Models.stake
    exact (Finset.sum_filter_add_sum_filter_not c (SlashedAt y.state ·) _).symm
  unfold reducedDrift stateDriftOn stateDrift referenceLoss referenceGain
  rw [loss, gain]
  omega

/-- With distinct keys, a key set weighs at most the validators that pass a test.

Every key of the set must be the key of a validator that passes the test.

Each key then weighs its own validator's effective balance, counted once. -/
private theorem keys_stake_le_validators {x : ForkedBeaconState preset}
    (unique : PubkeysDistinct x.state) (c : Finset BLSPubkey) (p : Validator → Bool)
    (keyed : ∀ k ∈ c, ∃ v ∈ x.state.validators.data.toList, v.pubkey = k ∧ p v = true) :
    Models.stake (effectiveWeight x.state) c ≤
      (x.state.validators.data.toList.map fun v =>
        if p v then v.effectiveBalance.toNat else 0).sum := by
  have distinct : (x.state.validators.data.toList.map (·.pubkey)).Nodup := unique
  let listed := x.state.validators.data.toList.filter (fun v => decide (v.pubkey ∈ c))
  have sameKeys : c = (listed.map (·.pubkey)).toFinset := by
    ext k
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, listed, decide_eq_true_eq]
    constructor
    · intro member
      obtain ⟨v, inside, key, _⟩ := keyed k member
      exact ⟨v, ⟨inside, key ▸ member⟩, key⟩
    · rintro ⟨v, ⟨_, member⟩, rfl⟩
      exact member
  have nodup : (listed.map (·.pubkey)).Nodup :=
    distinct.sublist (List.filter_sublist.map _)
  -- Each listed validator has its own weight, and passes the test.
  have counted : listed.map (fun v => effectiveWeight x.state v.pubkey) =
      listed.map (fun v => if p v then v.effectiveBalance.toNat else 0) := by
    refine List.map_congr_left fun v member => ?_
    obtain ⟨inside, keyIn⟩ := List.mem_filter.mp member
    obtain ⟨w, wListed, key, holds⟩ := keyed v.pubkey (of_decide_eq_true keyIn)
    have same : w = v := List.inj_on_of_nodup_map distinct wListed inside key
    subst same
    rw [effectiveWeight_of_member unique inside]
    simp [holds]
  unfold Models.stake
  rw [sameKeys, List.sum_toFinset _ nodup, List.map_map]
  change (listed.map (fun v => effectiveWeight x.state v.pubkey)).sum ≤ _
  rw [counted]
  exact (List.filter_sublist.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- The slashed common stake is paid from the scheduled keys' common reserve.

Each common key is the key of one scheduled index of `x`.

That index is unslashed and active, with an exit assigned before the cutoff.

When that key is slashed at `y`, it is not recent there.

So its common reserve is its effective balance at `x`. -/
theorem commonSlashed_le_commonReserve {x y : ForkedBeaconState preset}
    {high cutoff : Nat} (allocation : ScheduledAllocation x y high)
    (unique : PubkeysDistinct x.state) (uniqueY : PubkeysDistinct y.state)
    (early : x.fork < .glamsterdam) (within : cutoff ≤ high + 1)
    (finite : cutoff ≤ FAR_FUTURE_EPOCH.toNat)
    (apart : exitedBefore x cutoff ∩ recentKeys y.state = ∅) :
    commonSlashed x y (exitedBefore x cutoff) ≤
      ∑ i ∈ allocation.scheduled, allocation.commonReserve i := by
  have horizon : high + 1 ≤ horizonEnd x high := by
    unfold horizonEnd driftHorizon
    omega
  have distinct : (x.state.validators.data.toList.map (·.pubkey)).Nodup := unique
  have distinctY : (y.state.validators.data.toList.map (·.pubkey)).Nodup := uniqueY
  -- Each common key is the key of one validator of `x`, at an index.
  --
  -- That validator is active and unslashed, with an exit assigned before the cutoff.
  have indexed : ∀ k ∈ exitedBefore x cutoff, ∃ (i : Nat) (v : Validator),
      x.state.validators.data[i]? =
      some v ∧
      v.pubkey = k ∧ isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false ∧
      v.exitEpoch.toNat < cutoff := by
    intro k member
    unfold exitedBefore at member
    split at member
    · simp at member
    rw [Finset.mem_filter] at member
    obtain ⟨unslashed, u, listed, key, exits⟩ := member
    have active : k ∈ activeKeys x.state := (Finset.mem_filter.mp unslashed).1
    have clean : ¬ SlashedAt x.state k := (Finset.mem_filter.mp unslashed).2
    obtain ⟨i, w, found, wKey, wActive⟩ := (mem_keysAt_epoch early _ k).mp active
    have wListed : w ∈ x.state.validators.data.toList := by
      simpa using Array.mem_of_getElem? found
    have same : u = w := List.inj_on_of_nodup_map distinct listed wListed (key.trans wKey.symm)
    subst same
    refine ⟨i, u, found, key, wActive, ?_, exits⟩
    cases flag : u.slashed
    · rfl
    · exact absurd ⟨u, listed, key, flag⟩ clean
  let index : BLSPubkey → Nat := fun k =>
    if member : k ∈ exitedBefore x cutoff then Classical.choose (indexed k member) else 0
  have indexSpec : ∀ k (member : k ∈ exitedBefore x cutoff), ∃ v,
      x.state.validators.data[index k]? = some v ∧ v.pubkey = k ∧
        isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false ∧
        v.exitEpoch.toNat < cutoff := by
    intro k member
    simp only [index, member, ↓reduceDIte]
    exact Classical.choose_spec (indexed k member)
  let slashedCommon := (exitedBefore x cutoff).filter (SlashedAt y.state ·)
  -- Distinct common keys sit at distinct indices.
  have injective : Set.InjOn index slashedCommon := by
    intro k member l other same
    obtain ⟨v, found, key, _⟩ := indexSpec k (Finset.mem_filter.mp member).1
    obtain ⟨w, located, wKey, _⟩ := indexSpec l (Finset.mem_filter.mp other).1
    rw [same] at found
    obtain rfl := Option.some.inj (found.symm.trans located)
    exact key.symm.trans wKey
  -- Each such index is scheduled, and its common reserve is its effective balance.
  have reserved : ∀ k ∈ slashedCommon, index k ∈ allocation.scheduled ∧
      allocation.commonReserve (index k) = effectiveAt x (index k) := by
    intro k member
    obtain ⟨common, slashedY⟩ := Finset.mem_filter.mp member
    obtain ⟨v, found, key, active, clean, exits⟩ := indexSpec k common
    have scheduled : index k ∈ allocation.scheduled := by
      rw [allocation.exactScheduled, Finset.mem_filter]
      have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
        intro far
        have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        rw [far, farNat] at exits
        rw [farNat] at finite
        omega
      have before : v.exitEpoch.toNat ≤ horizonEnd x high := by omega
      refine ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, ?_⟩
      simp [found, active, clean, assigned, before]
    refine ⟨scheduled, ?_⟩
    obtain ⟨initial, w, initialAt, endpoint, sameKey, _⟩ :=
      allocation.endpointReads _ scheduled
    obtain rfl := Option.some.inj (initialAt.symm.trans found)
    obtain ⟨u, uListed, uKey, uSlashed⟩ := slashedY
    have wListed : w ∈ y.state.validators.data.toList := by
      simpa using Array.mem_of_getElem? endpoint
    have same : u = w := List.inj_on_of_nodup_map distinctY uListed wListed
      (uKey.trans (key.symm.trans sameKey))
    subst same
    have notRecent : initial.pubkey ∉ recentKeys y.state := fun recent =>
      (Finset.eq_empty_iff_forall_notMem.mp apart) initial.pubkey
        (Finset.mem_inter.mpr ⟨key ▸ common, recent⟩)
    rw [allocation.exactCommon _ scheduled u initial initialAt endpoint]
    simp [uSlashed, notRecent]
  have weight : ∀ k ∈ slashedCommon,
      effectiveWeight x.state k = effectiveAt x (index k) := by
    intro k member
    obtain ⟨v, found, key, _⟩ := indexSpec k (Finset.mem_filter.mp member).1
    subst key
    rw [effectiveWeight_of_member unique (by simpa using Array.mem_of_getElem? found)]
    simp [effectiveAt, found]
  unfold commonSlashed Models.stake
  calc ∑ k ∈ slashedCommon, effectiveWeight x.state k
      = ∑ k ∈ slashedCommon, allocation.commonReserve (index k) :=
        Finset.sum_congr rfl fun k member => (weight k member).trans (reserved k member).2.symm
    _ = ∑ i ∈ slashedCommon.image index, allocation.commonReserve i :=
        (Finset.sum_image injective).symm
    _ ≤ ∑ i ∈ allocation.scheduled, allocation.commonReserve i :=
        Finset.sum_le_sum_of_subset (fun i member => by
          obtain ⟨k, inside, rfl⟩ := Finset.mem_image.mp member
          exact (reserved k inside).1)

end

section

open Cryptography.Bls Uint64

/-- New boundary keys outside the initial reference.

They are previous-epoch support at `y` that is not active at `y`.

They are outside the unslashed reference at `x` and outside the initial previous-only keys. -/
def newBoundary (x y : ForkedBeaconState preset) : Finset BLSPubkey :=
  (recentKeys y.state \ activeKeys y.state) \ (unslashedKeys x.state ∪ previousOnly x)

/-- The gain outside the initial previous-only keys is held by issued tokens. -/
theorem gainWithoutPreviousOnly_le_issued {x y : ForkedBeaconState preset}
    {o : Ownership} {tokens : BLSPubkey → Finset TokenOrigin}
    (terminal : TerminalAllocation x y o tokens) :
    gainWithoutPreviousOnly x y ≤ o.issued.card := by
  obtain ⟨cards, _, total⟩ := terminal
  have same : gainWithoutPreviousOnly x y =
      ∑ k ∈ recentKeys y.state \ previousOnly x, (tokens k).card := by
    unfold gainWithoutPreviousOnly
    refine Finset.sum_congr rfl fun k member => ?_
    obtain ⟨_, _, _, _, card⟩ := cards k member
    exact card.symm
  rw [same, ← Finset.sum_inter_add_sum_sdiff _ (unslashedKeys x.state)]
  exact total

/-- New nonreference boundary stake and the gains of reference keys are disjoint.

Both are parts of the gain outside the initial previous-only keys. -/
private theorem nonreference_boundary_gain_le {x y : ForkedBeaconState preset}
    (keys : Finset BLSPubkey)
    (inside : keys ⊆ (recentKeys y.state \ previousOnly x) ∩ unslashedKeys x.state) :
    Models.stake (effectiveWeight y.state) (newBoundary x y) +
      ∑ k ∈ keys, (effectiveWeight y.state k - effectiveWeight x.state k) ≤
    gainWithoutPreviousOnly x y := by
  let g := fun k => effectiveWeight y.state k -
    Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k
  have reads (k : BLSPubkey) (member : k ∈ newBoundary x y) :
      k ∈ recentKeys y.state \ previousOnly x ∧ k ∉ unslashedKeys x.state := by
    simp only [newBoundary, Finset.mem_sdiff, Finset.mem_union, not_or] at member
    exact ⟨Finset.mem_sdiff.mpr ⟨member.1.1, member.2.2⟩, member.2.1⟩
  have apart : Disjoint (newBoundary x y) keys := by
    rw [Finset.disjoint_left]
    intro k member chosen
    exact (reads k member).2 (Finset.mem_inter.mp (inside chosen)).2
  have outer : Models.stake (effectiveWeight y.state) (newBoundary x y) =
      ∑ k ∈ newBoundary x y, g k := by
    unfold Models.stake
    refine Finset.sum_congr rfl fun k member => ?_
    simp only [g, Models.supported, (reads k member).2, ↓reduceIte, Nat.sub_zero]
  have inner : ∑ k ∈ keys, (effectiveWeight y.state k - effectiveWeight x.state k) =
      ∑ k ∈ keys, g k := by
    refine Finset.sum_congr rfl fun k member => ?_
    simp only [g, Models.supported, (Finset.mem_inter.mp (inside member)).2, ↓reduceIte]
  rw [outer, inner, ← Finset.sum_union apart]
  unfold gainWithoutPreviousOnly
  exact Finset.sum_le_sum_of_subset (Finset.union_subset (fun k member => (reads k member).1)
    fun k member => (Finset.mem_inter.mp (inside member)).1)

/-- The boundary gains of the new cohort are gains of distinct reference keys. -/
private theorem NewCohortCuts.boundary_keys {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {high : Nat} {ledger : LedgerCuts tail}
    (cuts : NewCohortCuts tail high ledger)
    (uniqueX : PubkeysDistinct x.state) (uniqueY : PubkeysDistinct y.state)
    (early : y.fork < .glamsterdam) :
    ∃ keys : Finset BLSPubkey,
      keys ⊆ (recentKeys y.state \ previousOnly x) ∩ unslashedKeys x.state ∧
      ∑ i ∈ cuts.boundary, (effectiveAt y i - effectiveAt x i) =
        ∑ k ∈ keys, (effectiveWeight y.state k - effectiveWeight x.state k) := by
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have kept := (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1
  have reads (i : Nat) (member : i ∈ cuts.boundary) : ∃ v w,
      x.state.validators.data[i]? = some v ∧ y.state.validators.data[i]? = some w ∧
      w.pubkey = v.pubkey ∧ isActiveValidator v (getCurrentEpoch x.state) = true ∧
      v.slashed = false ∧ w.pubkey ∈ recentKeys y.state \ activeKeys y.state := by
    have inBoundary := member
    rw [cuts.exactBoundary] at inBoundary
    obtain ⟨inCohort, onKey⟩ := Finset.mem_filter.mp inBoundary
    rw [cuts.exactUniverse] at inCohort
    obtain ⟨range, first, _⟩ := Finset.mem_filter.mp inCohort
    have index := Finset.mem_range.mp range
    let v := x.state.validators.data[i]
    have before : x.state.validators.data[i]? = some v := by simp [v, index]
    obtain ⟨w, after, key⟩ := validators_getElem?_of_validatorKeys_prefix kept before
    simp only [before, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at first
    simp only [after, Option.any_some, decide_eq_true_eq] at onKey
    exact ⟨v, w, before, after, key, first.1.1, first.1.2, onKey⟩
  let key : Nat → BLSPubkey := keyAt y.state
  refine ⟨cuts.boundary.image key, ?_, ?_⟩
  · intro k member
    obtain ⟨i, inBoundary, named⟩ := Finset.mem_image.mp member
    obtain ⟨v, w, before, after, same, active, clean, onKey⟩ := reads i inBoundary
    have keyed : key i = w.pubkey := by simp [key, keyAt, after]
    rw [← named, keyed]
    have activeX : w.pubkey ∈ activeKeys x.state := by
      unfold activeKeys
      exact (mem_keysAt_epoch xEarly _ _).mpr ⟨i, v, before, same.symm, active⟩
    have unslashed : w.pubkey ∈ unslashedKeys x.state := by
      unfold unslashedKeys
      refine Finset.mem_filter.mpr ⟨activeX, ?_⟩
      rw [same]
      exact not_slashedAt uniqueX (by simpa using Array.mem_of_getElem? before) clean
    refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp onKey).1, ?_⟩,
      unslashed⟩
    intro previous
    exact (Finset.mem_sdiff.mp previous).2 activeX
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun i member => ?_
      obtain ⟨v, w, before, after, same, _, _, _⟩ := reads i member
      have keyed : key i = w.pubkey := by simp [key, keyAt, after]
      rw [keyed, effectiveWeight_of_member uniqueY (by simpa using Array.mem_of_getElem? after),
        same, effectiveWeight_of_member uniqueX (by simpa using Array.mem_of_getElem? before)]
      simp [effectiveAt, before, after]
    · intro i first j second equal
      obtain ⟨_, u, _, uFound, _, _, _, _⟩ := reads i first
      obtain ⟨_, w, _, wFound, _, _, _, _⟩ := reads j second
      have keys : u.pubkey = w.pubkey := by simpa [key, keyAt, uFound, wFound] using equal
      exact uniqueY.index_eq uFound wFound keys

/-- Add twice the new nonreference boundary stake and twice the boundary gains of the new cohort.

The sum is within twice the new-boundary term of the drift. -/
theorem nonreference_boundary_le {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {high : Nat} {ledger : LedgerCuts tail}
    (cuts : NewCohortCuts tail high ledger)
    (uniqueX : PubkeysDistinct x.state) (uniqueY : PubkeysDistinct y.state)
    (early : y.fork < .glamsterdam)
    (funded : gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high) :
    2 * (Models.stake (effectiveWeight y.state) (newBoundary x y) +
      ∑ i ∈ cuts.boundary, (effectiveAt y i - effectiveAt x i)) ≤
    2 * max (windowEdgeLoad (config := config) x high) (gainBudget (config := config) x high) := by
  obtain ⟨keys, inside, same⟩ := cuts.boundary_keys uniqueX uniqueY early
  have gain := nonreference_boundary_gain_le keys inside
  have right :=
      le_max_right (windowEdgeLoad (config := config) x high) (gainBudget (config := config) x high)
  rw [same]
  omega

end

/-- Before Electra, this is the penalty bound of a branch with every floor proved.

The guard keeps the branch before Electra.

The cohort's penalty and sync debits fit the penalties of its epochs. -/
theorem penaltyProducer_pre {g x y : ForkedBeaconState preset}
    (before : x.fork < .pectra) :
    PenaltyProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail high supported twoSlots events replayed
  obtain ⟨genesis, parameters, caps, aligned, -, endEpoch, guard⟩ := id supported
  have notElectra : ¬ .pectra ≤ x.fork := Nat.not_le_of_gt before
  have early : y.fork < .pectra :=
    (guarded_fork_regime (shared.append tail) genesis high endEpoch guard).2.resolve_left
      notElectra
  have xEarly : x.fork < .glamsterdam := Nat.lt_trans before (by decide)
  refine (List.sum_le_sum fun e _ => producer_le_cohort x xEarly (floorPenaltyDebit · e)).trans ?_
  refine pre_run_penalties_upto shared tail high supported early ?_ (ix x y + 1) ?_ replayed
  · intro u head _ prior total read
    have within : (getCurrentEpoch u.state).toNat ≤ high + 1 := by omega
    have uEarly : u.fork < .pectra :=
      (guarded_fork_regime (shared.append head) genesis high within guard).2.resolve_left
        notElectra
    exact pre_floor_all_runs shared genesis parameters caps aligned guard twoSlots head uEarly
      within total read
  · exact steps_before_end tail

/-- The penalty bound of a branch in both fork regimes, like the balance floor of each key. -/
theorem penaltyProducer_proved {g x y : ForkedBeaconState preset} :
    PenaltyProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) :=
  if before : x.fork < .pectra then penaltyProducer_pre before
  else fun shared tail high supported twoSlots events replayed =>
    penaltyProducer_electra shared tail high supported twoSlots (Nat.le_of_not_lt before)
      events replayed

/-! ## Scheduled boundary growth within the exit-cohort growth

For each exit epoch through the end of the window, sum `cap - 2e` over the keys that exit there.

The exit-cohort growth takes the largest of these sums.

Each cap and effective balance is read at `x`.

A key with an assigned exit stays within its cap at `x`.

Before Electra, the guard keeps the whole window before the fork.

From Electra, its credentials never become compounding. -/

/-- On a supported branch, a key with an assigned exit at `x` stays within its cap at `x`. -/
private theorem scheduled_effective_le_cap {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt y i ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat := by
  obtain ⟨genesis, _, caps, _, early, endEpoch, guard⟩ := supported
  obtain ⟨w, read, credentials⟩ := tail.compounding_of_exit_assigned caps.activation
    caps.compounding early i v found assigned
  have cap := (shared.append tail).effectiveBalance_capped genesis caps.activation
    caps.compounding early w (Array.mem_of_getElem? read)
  have atEnd : effectiveAt y i = w.effectiveBalance.toNat := by simp [effectiveAt, read]
  have regime := (guarded_fork_regime (shared.append tail) genesis high endEpoch guard).2
  have kept : withdrawalMaxEffectiveBalance preset y.fork w ≤
      withdrawalMaxEffectiveBalance preset x.fork v := by
    rcases regime with electra | before
    · have later : Fork.pectra ≤ y.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
      simp only [withdrawalMaxEffectiveBalance, later, electra, ↓reduceIte,
        getMaxEffectiveBalance]
      by_cases compound : hasCompoundingWithdrawalCredential w = true
      · simp only [compound, credentials compound, ↓reduceIte]
        exact UInt64.le_refl _
      · simp only [compound, Bool.false_eq_true, ↓reduceIte]
        split
        · exact caps.compounding
        · exact UInt64.le_refl _
    · have xBefore := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) before
      have yNot : ¬ Fork.pectra ≤ y.fork := Nat.not_le_of_gt before
      have xNot : ¬ Fork.pectra ≤ x.fork := Nat.not_le_of_gt xBefore
      simp only [withdrawalMaxEffectiveBalance, yNot, xNot, ↓reduceIte]
      exact UInt64.le_refl _
  rw [atEnd]
  exact (UInt64.le_iff_toNat_le.mp cap).trans (UInt64.le_iff_toNat_le.mp kept)

/-- A sum over list positions is the sum over the list. -/
private theorem sum_range_getElem? (F : Validator → Nat) (l : List Validator) :
    ∑ i ∈ Finset.range l.length, ((l[i]?).map F).getD 0 = (l.map F).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [ih, Nat.add_comm]

/-- One exit cohort's residual is at most the exit-cohort growth. -/
private theorem cohort_le_Rhat (x : ForkedBeaconState preset) (high j : Nat)
    (within : j ≤ horizonEnd x high) :
    (x.state.validators.data.toList.map fun v =>
      if isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = j) then
        (withdrawalMaxEffectiveBalance preset x.fork v).toNat - 2 * v.effectiveBalance.toNat
      else 0).sum ≤ exitCohortGrowth x high := by
  unfold exitCohortGrowth
  apply Serialization.Ssz.member_le_foldl_max
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le within), rfl⟩

/-- Endpoint-epoch exits grow within the exit-cohort growth. -/
theorem scheduledBoundaryProducer {g x y : ForkedBeaconState preset} :
    ScheduledBoundaryProducer (config := config) (checks := checks) (g := g) (x := x)
      (y := y) := by
  intro shared tail high supported twoSlots j _ within current
  let P : Validator → Bool := fun v =>
    isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
      decide (v.exitEpoch.toNat = j)
  let F : Validator → Nat := fun v =>
    if P v then
      (withdrawalMaxEffectiveBalance preset x.fork v).toNat - 2 * v.effectiveBalance.toNat
    else 0
  have termwise : ∀ i ∈ Finset.range x.state.validators.data.size,
      (if (x.state.validators.data[i]?).any P then effectiveAt y i - 2 * effectiveAt x i
        else 0) ≤ ((x.state.validators.data.toList[i]?).map F).getD 0 := by
    intro i _
    rw [Array.getElem?_toList]
    cases found : x.state.validators.data[i]? with
    | none => simp
    | some v =>
      simp only [Option.any_some, Option.map_some, Option.getD_some, F]
      split
      · rename_i selected
        have exitEq : v.exitEpoch.toNat = j := by
          simp only [P, Bool.and_eq_true, decide_eq_true_eq] at selected
          exact selected.2
        have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
          have same : v.exitEpoch = getCurrentEpoch y.state :=
            UInt64.toNat_inj.mp (exitEq.trans current.symm)
          rw [same]
          exact getCurrentEpoch_ne_farFuture twoSlots y.state
        have bound := scheduled_effective_le_cap shared tail high supported i v found assigned
        have atStart : effectiveAt x i = v.effectiveBalance.toNat := by
          simp [effectiveAt, found]
        omega
      · exact Nat.zero_le _
  calc _ ≤ ∑ i ∈ Finset.range x.state.validators.data.size,
        ((x.state.validators.data.toList[i]?).map F).getD 0 := Finset.sum_le_sum termwise
    _ = (x.state.validators.data.toList.map F).sum := by
        rw [← Array.length_toList]
        exact sum_range_getElem? F _
    _ ≤ exitCohortGrowth x high := cohort_le_Rhat x high j within

section

open Cryptography.Bls

/-- Queueing a consolidation keeps the balances and the slot.

It changes only the source's exit and withdrawable epochs.

The exit is after the current epoch, and the source can withdraw exactly the delay after it.

The call it makes spends the source balance before it changes the exit epoch. -/
private theorem queueConsolidation_facts {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    t.balances = s.balances ∧ t.slot = s.slot ∧
      ∃ exitEpoch withdrawableEpoch : Epoch, getCurrentEpoch s < exitEpoch ∧
        withdrawableEpoch.toNat =
          exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ∧
        t.validators.data[sourceIndex.toNat]? =
          some { source with exitEpoch := exitEpoch, withdrawableEpoch := withdrawableEpoch } ∧
        ∀ k, k ≠ sourceIndex.toNat → t.validators.data[k]? = s.validators.data[k]? := by
  have balances := queueConsolidation_balances ok
  have slot := (frame_queueConsolidation found ok).slot
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨churned, epoch⟩, called, withdrawable, withdrawableOk, changed, set, _, _, rfl⟩ := ok
  -- The churn call opens no earlier than the first exit epoch, after the current one.
  obtain ⟨first, firstOk⟩ : ∃ first,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first := by
    have opened := called
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith,
      mapError_ok_iff] at opened
    obtain ⟨first, firstOk, -⟩ := opened
    exact ⟨first, firstOk⟩
  have firstLe := (computeConsolidationEpochAndUpdateChurn_first firstOk called).1
  have firstNat := (computeActivationExitEpoch_ok_iff.mp firstOk).2
  have withdrawableNat := (Uint64.addChecked_ok_iff.mp withdrawableOk).2
  simp only at withdrawableNat
  obtain ⟨_, validators, _⟩ := computeConsolidationEpochAndUpdateChurn_earliest called
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨balances, slot, epoch, withdrawable, ?_, withdrawableNat, ?_, ?_⟩
  · exact UInt64.lt_iff_toNat_lt.mpr
      (by have := UInt64.le_iff_toNat_le.mp firstLe; omega)
  · simp [BeaconState.putValidator]
  · intro k different
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
    rw [Array.getElem?_set_ne _ (Ne.symm different), validators]

/-- Queueing an unslashed, active source with no exit keeps the reserve cut at the current epoch.

The new entry is appended to the queue.

The source stays supported at the current epoch.

So it was already relevant and bounded at the input.

Its new withdrawable epoch is after the current epoch, so it is not due.

Every other validator and every balance is unchanged. -/
private theorem reserveCut_queueConsolidation {x : ForkedBeaconState preset} {high : Nat}
    {fork : Fork} {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    {suffix : List PendingConsolidation} {o : Ownership}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (active : isActiveValidator source (getCurrentEpoch s) = true)
    (clean : source.slashed = false) (unset : source.exitEpoch = FAR_FUTURE_EPOCH)
    (life : RegistryLifecycle x.state s)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) suffix o) :
    ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch s)
      (suffix ++ [⟨sourceIndex, targetIndex⟩]) o := by
  obtain ⟨balances, _, exitEpoch, withdrawableEpoch, later, delayed, atSource, others⟩ :=
    queueConsolidation_facts found ok
  have ordered : exitEpoch ≤ withdrawableEpoch := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨valid, wasRetired, original, reference, scheduled, pending, due, idle, activePending,
    endpoint⟩ := reserve
  have supported : SupportedAt (getCurrentEpoch s) source := ⟨clean, Or.inl active⟩
  -- Each validator after the step is the one before it, or the source with its new epochs.
  have lookup : ∀ k w, t.validators.data[k]? = some w →
      (k ≠ sourceIndex.toNat ∧ s.validators.data[k]? = some w) ∨
        (k = sourceIndex.toNat ∧
          w = { source with exitEpoch := exitEpoch, withdrawableEpoch := withdrawableEpoch }) := by
    intro k w read
    by_cases same : k = sourceIndex.toNat
    · subst same
      exact Or.inr ⟨rfl, (Option.some.inj (read.symm.trans atSource))⟩
    · exact Or.inl ⟨same, (others k same) ▸ read⟩
  have balanceSame : ∀ k, actualBalanceAt ⟨fork, t⟩ k = actualBalanceAt ⟨fork, s⟩ k := by
    intro k
    simp only [actualBalanceAt, balances]
  have effectiveSame : ∀ k, effectiveAt ⟨fork, t⟩ k = effectiveAt ⟨fork, s⟩ k := by
    intro k
    by_cases same : k = sourceIndex.toNat
    · subst same
      simp only [effectiveAt, atSource, found, Option.map_some, Option.getD_some]
    · simp only [effectiveAt, others k same]
  have capSame : withdrawalMaxEffectiveBalance preset fork
      { source with exitEpoch := exitEpoch, withdrawableEpoch := withdrawableEpoch } =
      withdrawalMaxEffectiveBalance preset fork source := rfl
  -- An entry of the longer queue at another index is an entry of the old queue.
  have queued : ∀ k, k ≠ sourceIndex.toNat →
      (∃ c ∈ suffix ++ [⟨sourceIndex, targetIndex⟩], c.sourceIndex.toNat = k) →
        ∃ c ∈ suffix, c.sourceIndex.toNat = k := by
    intro k different ⟨c, member, index⟩
    rcases List.mem_append.mp member with old | new
    · exact ⟨c, old, index⟩
    · simp only [List.mem_singleton] at new
      subst new
      exact absurd index.symm different
  -- Funding relevance after the step gives funding relevance before it.
  have relevant : ∀ k, FundingRelevant ⟨fork, t⟩ (getCurrentEpoch s)
      (suffix ++ [⟨sourceIndex, targetIndex⟩]) k →
      FundingRelevant ⟨fork, s⟩ (getCurrentEpoch s) suffix k := by
    intro k ⟨w, read, support⟩
    rcases lookup k w read with ⟨different, before⟩ | ⟨rfl, -⟩
    · refine ⟨w, before, ?_⟩
      rcases support with now | waiting | inQueue
      · exact Or.inl now
      · exact Or.inr (Or.inl waiting)
      · exact Or.inr (Or.inr (queued k different inQueue))
    · exact ⟨source, found, Or.inl supported⟩
  refine ⟨valid, ?_, original, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- The source is supported now, so it is not retired, and no other entry moved.
  · intro k member w read
    rcases lookup k w read with ⟨different, before⟩ | ⟨rfl, -⟩
    · obtain ⟨unsupported, absent⟩ := wasRetired k member w before
      exact ⟨unsupported, fun inQueue => absent (queued k different inQueue)⟩
    · exact absurd supported ((wasRetired _ member source found).1 _ (UInt64.le_refl _))
  · intro k ref notRetired support
    rw [effectiveSame, balanceSame]
    exact reference k ref notRetired (relevant k support)
  -- The source had no exit at `x`, so it is not a scheduled key.
  · intro k initial w initialAt activeX cleanX assigned read support
    rcases lookup k w read with ⟨_, before⟩ | ⟨rfl, -⟩
    · rw [effectiveSame, balanceSame]
      exact scheduled k initial w initialAt activeX cleanX assigned before support
    · obtain ⟨atS, located, epochs⟩ := life.validators _ initial initialAt
      obtain rfl := Option.some.inj (located.symm.trans found)
      exact absurd ((epochs.exitEpoch assigned).symm.trans unset) assigned
  · intro k initial notRetired support w read
    rw [balanceSame]
    rcases lookup k w read with ⟨_, before⟩ | ⟨rfl, rfl⟩
    · exact pending k initial notRetired (relevant k support) w before
    · rw [capSame]
      exact pending _ initial notRetired (relevant _ support) source found
  -- The source's new withdrawable epoch is after the current epoch, so it is not due.
  · intro c member w read ready notRef
    rcases lookup _ w read with ⟨different, before⟩ | ⟨same, rfl⟩
    · rcases List.mem_append.mp member with old | new
      · rw [balanceSame]
        exact due c old w before ready notRef
      · simp only [List.mem_singleton] at new
        subst new
        exact absurd rfl different
    · exact absurd ready (UInt64.not_le.mpr (UInt64.lt_of_lt_of_le later ordered))
  · intro k w read notRef notQueued quiet support
    rw [effectiveSame, balanceSame]
    rcases lookup k w read with ⟨different, before⟩ | ⟨rfl, rfl⟩
    · refine idle k w before notRef notQueued quiet ?_
      rcases support with now | waiting | ⟨inQueue, fresh⟩
      · exact Or.inl now
      · exact Or.inr (Or.inl waiting)
      · exact Or.inr (Or.inr ⟨queued k different inQueue, fresh⟩)
    · rw [capSame]
      exact idle _ source found notRef notQueued quiet (Or.inl supported)
  · intro k initial w initialX read atX activeX notRetired support
    rw [effectiveSame, balanceSame]
    rcases lookup k w read with ⟨_, before⟩ | ⟨rfl, rfl⟩
    · exact activePending k initial w initialX before atX activeX notRetired (relevant k support)
    · rw [capSame]
      exact activePending _ initial source initialX found atX activeX notRetired
        (relevant _ support)
  · intro k w read support notPrevious
    rw [effectiveSame]
    rcases lookup k w read with ⟨_, before⟩ | ⟨rfl, rfl⟩
    · exact endpoint k w before support notPrevious
    · exact endpoint _ source found supported notPrevious

/-- Queueing a consolidation keeps the future cover.

The source is active, so it is not a key still to activate, and every other key is unchanged. -/
private theorem futureCover_queueConsolidation {x : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator} {o : Ownership}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (active : isActiveValidator source (getCurrentEpoch s) = true)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (future : FutureEffectiveCover x ⟨fork, s⟩ o) :
    FutureEffectiveCover x ⟨fork, t⟩ o := by
  obtain ⟨_, slot, _, _, _, _, atSource, others⟩ := queueConsolidation_facts found ok
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  refine futureCover_mono (u := ⟨fork, s⟩) ?_ (fun _ => Nat.le_refl _) future
  intro k w read waiting clean notExited
  by_cases same : k = sourceIndex.toNat
  · -- The source activated by the current epoch, so it is not waiting.
    subst same
    obtain rfl := Option.some.inj (read.symm.trans atSource)
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
    simp only [epoch] at waiting
    exact absurd active.1 (UInt64.not_le.mpr waiting)
  · have before : s.validators.data[k]? = some w := (others k same) ▸ read
    refine ⟨w, before, epoch ▸ waiting, clean, notExited, rfl, ?_⟩
    simp [effectiveAt, read, before]

/-- The reserved replay of one consolidation request of a block.

The request does one of three things.

It returns its state, or it switches one validator to compounding credentials.

Otherwise, it queues an accepted source.

- Returning the state keeps everything.
- The switch is the reserved replay of a switch to compounding, here `switched`.
- Queueing appends a fresh tag for the call it makes.
  An accepted source is active with no exit.
  So by `slashedExit` it is unslashed and supported at the current epoch.
  Its reserve was already bounded, and it is not due.
  Its assignment bound is `assigned`.

The ownership is unchanged in every case. -/
theorem reservedReplay_consolidationRequest {fork : Fork} {s t : BeaconState preset fork}
    {request : ConsolidationRequest}
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, s⟩ (getCurrentEpoch s) (getCurrentEpoch s) queue owned owned)
    (retired : RetiredActivated s owned.retired)
    (cover : EndpointCoverAll x ⟨fork, s⟩ owned)
    (future : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (life : RegistryLifecycle x.state s)
    (electra : .pectra ≤ fork)
    (ok : processConsolidationRequest config s electra request = .ok t)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (slashedExit : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (assigned : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch = FAR_FUTURE_EPOCH →
      (∃ w, t.validators.data[i]? = some w ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH) →
      owned.original i ≤ v.effectiveBalance.toNat + rounding i)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (callOf : ∀ (sourceIndex targetIndex : ValidatorIndex) (source : Validator),
      queueConsolidation config s electra sourceIndex source targetIndex = .ok t →
      ∃ call : DepartureQueueCall,
        call.amount = source.effectiveBalance ∧
        call.earliest = s.earliestConsolidationEpoch electra ∧
        call.available = s.consolidationBalanceToConsume electra ∧
        call.epoch = t.earliestConsolidationEpoch electra ∧
        call.left = t.consolidationBalanceToConsume electra ∧
        getConsolidationChurnLimit config s = .ok call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first ∧
        ∃ next, getValidator t sourceIndex = .ok next ∧ next.exitEpoch = call.epoch)
    (switched : ∀ index : ValidatorIndex, switchToCompoundingValidator s electra index = .ok t →
      ∀ e : BalanceEvent preset, e.before = ⟨fork, s⟩ → e.after = ⟨fork, t⟩ →
      e.source ≠ .consolidations →
      ReservedReplay (config := config) (checks := checks) x high rounding
          ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, t⟩ (getCurrentEpoch t)
          eventPosition paymentPosition callPosition [e] queue queue [] [] [] owned owned ∧
        ReservedFrame (config := config) (checks := checks) x high rounding
          ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue owned owned ∧
        RetiredActivated t owned.retired ∧
        EndpointCoverAll x ⟨fork, t⟩ owned ∧ FutureEffectiveCover x ⟨fork, t⟩ owned) :
    ∃ (queue' : List TaggedEntry) (calls' : List (IndexedDepartureCall preset config))
      (owned' : Ownership),
      ReservedReplay (config := config) (checks := checks) x high rounding
        ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, t⟩ (getCurrentEpoch t)
        eventPosition paymentPosition callPosition
        [⟨.excess, ⟨fork, s⟩, ⟨fork, t⟩, 0,
          match findValidatorByPubkey s request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat⟩]
        queue queue' [] [] calls' owned owned' ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue' owned' owned' ∧
      RetiredActivated t owned'.retired ∧
      EndpointCoverAll x ⟨fork, t⟩ owned' ∧ FutureEffectiveCover x ⟨fork, t⟩ owned' ∧
      (∀ electra' : .pectra ≤ fork, DepartureQueueTrace
        (s.earliestConsolidationEpoch electra') (s.consolidationBalanceToConsume electra')
        (calls'.map (·.call))
        (t.earliestConsolidationEpoch electra') (t.consolidationBalanceToConsume electra')) ∧
      ConsolidationCallSites preset config calls' [⟨fork, s⟩] ∧
      (∀ tag ∈ queue', tag ∉ queue → (∃ n, tag.tag = .fresh n) ∧
        ∃ v, t.validators.data[tag.entry.sourceIndex.toNat]? = some v ∧
          v.exitEpoch.toNat = tag.epoch ∧ v.exitEpoch ≠ FAR_FUTURE_EPOCH) ∧
      (calls' = [] ∨
        (t.pendingConsolidations electra).data.size ≠
          (s.pendingConsolidations electra).data.size) := by
  have slot := (frame_processConsolidationRequest ok).slot
  have sameEpoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  -- The debit limit of the recorded event is read at `s`.
  generalize (match findValidatorByPubkey s request.sourcePubkey with
      | none => 0
      | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) = debit
  have notTransfer : BalanceSource.excess ≠ .consolidations := by decide
  obtain ⟨_, _, ownedFrame, assignment, _, erasure, _, reserve, _⟩ := id frame
  have ownedEvent : OwnedEvent eventPosition paymentPosition
      ⟨.excess, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩ [] [] owned owned := by
    unfold OwnedEvent
    simp only [notTransfer, ↓reduceIte]
    exact ⟨by trivial, by trivial, Or.inr (OwnedFrame.refl ownedFrame.1)⟩
  rcases consolidationRequest_cases ok with same | ⟨index, switch⟩ |
    ⟨sourceIndex, source, targetIndex, target, accepted, queued⟩
  -- The request returned its state: the event keeps the queue and the ownership.
  · subst t
    have tagged : TagEvent (config := config) ⟨.excess, ⟨fork, s⟩, ⟨fork, s⟩, 0, debit⟩
        callPosition queue queue [] [] [] :=
      ⟨erasure, erasure, Or.inl ⟨notTransfer, rfl, rfl, rfl, rfl⟩⟩
    have event : ReservedEvent x high eventPosition paymentPosition rounding
        ⟨.excess, ⟨fork, s⟩, ⟨fork, s⟩, 0, debit⟩ queue queue [] [] owned owned := by
      refine ⟨ownedEvent, assignment, assignment, ?_⟩
      simp only [notTransfer, ↓reduceIte]
      exact ⟨reserve, reserve⟩
    exact ⟨queue, [], owned,
      ReservedReplay.singleton_nonconsolidation notTransfer frame tagged event,
      frame, retired, cover, future, fun _ => .nil _ _, by simp [ConsolidationCallSites],
      fun _ member old => absurd member old, .inl rfl⟩
  -- The switch is the producer's transport.
  · obtain ⟨replay, after, retiredT, coverT, futureT⟩ :=
      switched index switch ⟨.excess, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩ rfl rfl notTransfer
    -- The switch keeps the consolidation churn state.
    obtain ⟨_, sameEarliest, sameLeft⟩ := switchToCompoundingValidator_consolidationQueues switch
    exact ⟨queue, [], owned, replay, after, retiredT, coverT, futureT,
      fun _ => by rw [sameEarliest, sameLeft]; exact .nil _ _, by simp [ConsolidationCallSites],
      fun _ member old => absurd member old, .inl rfl⟩
  -- The request queued an accepted source, which is active with no exit and so unslashed.
  · have found := accepted.sourceAt
    have active := accepted.sourceActive
    have unset := accepted.sourceStays
    have clean : source.slashed = false := by
      cases flag : source.slashed
      · rfl
      · exact absurd unset (slashedExit _ source found flag)
    obtain ⟨_, _, exitEpoch, withdrawableEpoch, _, delayed, atSource, _⟩ :=
      queueConsolidation_facts found queued
    -- The call is DepartureQueue's, and the source's new exit is its epoch.
    obtain ⟨call, amount, earliest, available, epoch, left, rate, first, next, nextRead,
      nextExit⟩ := callOf sourceIndex targetIndex source queued
    obtain rfl := Option.some.inj ((getValidator_eq_ok_iff.mp nextRead).symm.trans atSource)
    let called : IndexedDepartureCall preset config :=
      ⟨some sourceIndex.toNat, call, none, by simp, by simp⟩
    let tag : TaggedEntry :=
      ⟨⟨sourceIndex, targetIndex⟩, .fresh callPosition, call.amount.toNat, call.epoch.toNat⟩
    have erasureT : QueueErasure (queue ++ [tag]) (pendingQueue ⟨fork, t⟩) := by
      unfold QueueErasure at erasure ⊢
      simp only [pendingQueue, electra, ↓reduceDIte] at erasure ⊢
      rw [queueConsolidation_pendingConsolidations queued, ← erasure, List.map_append]
      rfl
    have tagged : TagEvent (config := config) ⟨.excess, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩
        callPosition queue (queue ++ [tag]) [] [] [called] :=
      ⟨erasure, erasureT, Or.inr (Or.inl ⟨fork, s, t, electra, request, sourceIndex, source,
        targetIndex, called, rfl, rfl, rfl, ok, getValidator_eq_ok_iff.mpr found, queued, rfl,
        amount, earliest, available, epoch, left, first, rate, rfl, rfl, rfl, rfl⟩)⟩
    have reserveT : ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch t)
        ((queue ++ [tag]).map (·.entry)) owned := by
      rw [sameEpoch, List.map_append]
      exact reserveCut_queueConsolidation found active clean unset life queued reserve
    have sourceExit : ∃ w, t.validators.data[sourceIndex.toNat]? = some w ∧
        w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      refine ⟨_, atSource, fun far => ?_⟩
      have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      have bounded := withdrawableEpoch.toNat_lt
      simp only at far
      rw [far, farNat] at delayed
      omega
    have assignmentT : AssignmentCut rounding (queue ++ [tag]) owned :=
      assignmentCut_append_fresh assignment (fun added member _ _ => by
        simp only [List.mem_singleton] at member
        subst member
        simpa only [tag, amount] using assigned _ source found unset sourceExit)
    have event : ReservedEvent x high eventPosition paymentPosition rounding
        ⟨.excess, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩ queue (queue ++ [tag]) [] [] owned owned := by
      refine ⟨ownedEvent, assignment, assignmentT, ?_⟩
      simp only [notTransfer, ↓reduceIte]
      exact ⟨reserve, reserveT⟩
    have last := reservedFrame_refl (config := config) (checks := checks)
      reserveT assignmentT erasureT
    have replay := ReservedReplay.cons (eventPosition := eventPosition)
      (paymentPosition := paymentPosition) frame tagged event (.nil (by exact last))
    have trace : ∀ electra' : .pectra ≤ fork, DepartureQueueTrace
        (s.earliestConsolidationEpoch electra') (s.consolidationBalanceToConsume electra')
        ([called].map (·.call))
        (t.earliestConsolidationEpoch electra') (t.consolidationBalanceToConsume electra') := by
      intro _
      have one := DepartureQueueTrace.cons call (DepartureQueueTrace.nil call.epoch call.left)
      rw [earliest, available, epoch, left] at one
      exact one
    have sites : ConsolidationCallSites preset config [called] [⟨fork, s⟩] := by
      intro c member
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨_, List.mem_singleton_self _, first, rate⟩
    -- The appended tag's epoch is its source's new exit.
    have fresh : ∀ added ∈ queue ++ [tag], added ∉ queue → (∃ n, added.tag = .fresh n) ∧
        ∃ v, t.validators.data[added.entry.sourceIndex.toNat]? = some v ∧
          v.exitEpoch.toNat = added.epoch ∧ v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro added member old
      rcases List.mem_append.mp member with inQueue | new
      · exact absurd inQueue old
      simp only [List.mem_singleton] at new
      subst new
      refine ⟨⟨callPosition, rfl⟩, _, atSource, ?_⟩
      refine ⟨by simp only [tag, ← nextExit], fun far => ?_⟩
      -- A checked add of a positive delay leaves the exit below the far future.
      have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      have bounded := withdrawableEpoch.toNat_lt
      simp only at far
      rw [far, farNat] at delayed
      omega
    refine ⟨queue ++ [tag], [called], owned, by simpa only [List.append_nil] using replay, last,
      RetiredActivated.lifecycle (registryLifecycle_processConsolidationRequest ok) retired,
      endpointCover_processConsolidationRequest compounding ok cover,
      futureCover_queueConsolidation found active queued future, trace, sites, fresh, .inr ?_⟩
    -- The queued request appends one pending consolidation.
    have grown := congrArg List.length (queueConsolidation_pendingConsolidations queued)
    simp only [Array.length_toList, List.length_append, List.length_singleton] at grown
    omega

/-- The stake of one exit cohort within the horizon is at most `Bd`.

`Bd` is the largest effective balance that exits in two adjacent epochs of the window. -/
private theorem cohort_le_Bd (x : ForkedBeaconState preset) {high t : Nat}
    (within : t ≤ driftHorizon x high) :
    (x.state.validators.data.toList.map fun v =>
      if v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t ∨
          v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t + 1 then
        v.effectiveBalance.toNat else 0).sum ≤ adjacentExitStake x (driftHorizon x high) := by
  unfold adjacentExitStake
  apply le_foldr_max
  exact List.mem_map.mpr ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le within), rfl⟩

/-- The stake of the keys active only at the previous epoch is at most `Bd`.

A validator active only at the previous epoch exits at the current one. -/
private theorem B0_le_Bd (x : ForkedBeaconState preset) (high : Nat) : previousOnlyStake x ≤
    adjacentExitStake x (driftHorizon x high) := by
  refine le_trans ?_ (cohort_le_Bd x (t := 0) (Nat.zero_le _))
  unfold previousOnlyStake
  apply List.sum_le_sum
  intro v _
  have px := getPreviousEpoch_toNat x.state
  by_cases leaving : isActiveValidator v (getPreviousEpoch x.state) &&
      !isActiveValidator v (getCurrentEpoch x.state)
  · have exits : v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + 0 := by
      simp only [isActiveValidator, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
        UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at leaving
      omega
    simp [leaving, exits]
  · simp only [leaving]
    exact Nat.zero_le _

/-- Take the previous-only keys still recent at `y` and the initially scheduled boundary of `y`.

Together they fit the stake of the previous-only keys plus twice `Bd`.

Each previous-only key exits at the epoch of `x`.

So it stays recent only while `y` is in that epoch.

There it counts once as gain and twice as boundary, and its effective balance has not risen.

Above that epoch, take the active keys of `x` that exit at the epoch of `y`.

They are one exit cohort within the horizon, which `Bd` bounds. -/
theorem oldBoundary_le {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    3 * Models.stake (effectiveWeight y.state) (recentKeys y.state ∩ previousOnly x) +
      2 * (∑ i ∈ Finset.range x.state.validators.data.size,
        if (x.state.validators.data[i]?).any (fun v =>
            isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
            decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
        then effectiveAt x i else 0) ≤
    previousOnlyStake x + 2 * adjacentExitStake x (driftHorizon x high) := by
  obtain ⟨genesis, _, _, _, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have uniqueX := shared.pubkeysDistinct genesis
  have uniqueY := (shared.append tail).pubkeysDistinct genesis
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  set E := (getCurrentEpoch x.state).toNat with hE
  set Ey := (getCurrentEpoch y.state).toNat with hEy
  -- The scheduled boundary of `y` is one exit cohort of `x` within the horizon.
  set scheduled := ∑ i ∈ Finset.range x.state.validators.data.size,
    if (x.state.validators.data[i]?).any (fun v =>
        isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
        decide (v.exitEpoch.toNat = Ey))
    then effectiveAt x i else 0 with hScheduled
  let test (v : Validator) : Bool := isActiveValidator v (getCurrentEpoch x.state) &&
    !v.slashed && decide (v.exitEpoch.toNat = Ey)
  have asList : scheduled = (x.state.validators.data.toList.map fun v =>
      if test v then v.effectiveBalance.toNat else 0).sum := by
    rw [hScheduled, ← sum_range_getElem?]
    simp only [Array.length_toList, Array.getElem?_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases found : x.state.validators.data[i]? <;> simp [effectiveAt, found, test]
  have scheduledLe : scheduled ≤ adjacentExitStake x (driftHorizon x high) := by
    have within : Ey - E ≤ driftHorizon x high := by
      unfold driftHorizon
      omega
    refine le_trans ?_ (cohort_le_Bd x within)
    rw [asList]
    apply List.sum_le_sum
    intro v _
    by_cases chosen : test v = true
    · have exits : v.exitEpoch.toNat = E + (Ey - E) := by
        simp only [test, Bool.and_eq_true, decide_eq_true_eq] at chosen
        omega
      simp only [chosen, ↓reduceIte]
      split
      · exact Nat.le_refl _
      · rename_i outside
        exact absurd (Or.inl (by omega)) outside
    · simp only [Bool.not_eq_true] at chosen
      simp only [chosen, Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _
  -- A previous-only key recent at `y` keeps the epoch of `x` and its effective balance.
  have carried : ∀ k ∈ recentKeys y.state ∩ previousOnly x,
      Ey = E ∧ effectiveWeight y.state k ≤ effectiveWeight x.state k := by
    intro k member
    obtain ⟨recentY, only⟩ := Finset.mem_inter.mp member
    obtain ⟨before, notNow⟩ := Finset.mem_sdiff.mp only
    have unslashedX : ¬ SlashedAt x.state k := fun slashed =>
      (Finset.mem_filter.mp recentY).2 (slashedAt_forward tail slashed)
    have recentX : k ∈ recentKeys x.state :=
      Finset.mem_filter.mpr ⟨Finset.mem_union_right _ before, unslashedX⟩
    have same := recent_inactive_same_epoch shared tail genesis twoSlots early
      (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨recentY, recentX⟩, notNow⟩)
    refine ⟨congrArg UInt64.toNat same, ?_⟩
    obtain ⟨i, old, found, keyEq, _⟩ := (mem_keysAt_epoch xEarly _ k).mp before
    obtain ⟨v, current, vKey⟩ := validators_getElem?_of_validatorKeys_prefix
      (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have bound : effectiveAt y i ≤ effectiveAt x i := by
      rcases (guarded_fork_regime (shared.append tail) genesis high endEpoch guard).2 with
        _ | before
      · exact (run_same_epoch_effective tail early same i inside).le
      · exact tail.effectiveAt_le_of_same_epoch before same i inside
    have oldWeight := effectiveWeight_of_member uniqueX
      (by simpa using Array.mem_of_getElem? found)
    have newWeight := effectiveWeight_of_member uniqueY
      (by simpa using Array.mem_of_getElem? current)
    rw [keyEq] at oldWeight
    rw [vKey, keyEq] at newWeight
    rw [oldWeight, newWeight]
    simpa [effectiveAt, found, current] using bound
  have previousLe : Models.stake (effectiveWeight y.state) (recentKeys y.state ∩ previousOnly x) ≤
      previousOnlyStake x := by
    unfold Models.stake
    calc _ ≤ ∑ k ∈ recentKeys y.state ∩ previousOnly x, effectiveWeight x.state k :=
          Finset.sum_le_sum fun k member => (carried k member).2
      _ ≤ ∑ k ∈ previousOnly x, effectiveWeight x.state k :=
          Finset.sum_le_sum_of_subset (Finset.inter_subset_right)
      _ ≤ previousOnlyStake x := by
          refine keys_stake_le_validators uniqueX (previousOnly x)
            (fun v => isActiveValidator v (getPreviousEpoch x.state) &&
              !isActiveValidator v (getCurrentEpoch x.state)) fun k member => ?_
          -- A previous-only key names a validator active at the previous epoch only.
          obtain ⟨before, notNow⟩ := Finset.mem_sdiff.mp member
          obtain ⟨i, v, found, key, activeBefore⟩ := (mem_keysAt_epoch xEarly _ k).mp before
          refine ⟨v, by simpa using Array.mem_of_getElem? found, key, ?_⟩
          have inactive : isActiveValidator v (getCurrentEpoch x.state) = false := by
            by_contra activeNow
            exact notNow ((mem_keysAt_epoch xEarly _ k).mpr
              ⟨i, v, found, key, by simpa using activeNow⟩)
          simp [activeBefore, inactive]
  have b0 := B0_le_Bd x high
  by_cases stayed : Ey = E
  · -- In the epoch of `x` no key active at `x` exits, so the scheduled boundary is empty.
    have empty : scheduled = 0 := by
      rw [asList]
      refine List.sum_eq_zero fun n member => ?_
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
      have quiet : test v = false := by
        simp only [test, isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
        omega
      simp [quiet]
    change 3 * _ + 2 * scheduled ≤ _
    omega
  · -- Above the epoch of `x` no previous-only key is recent.
    have none : recentKeys y.state ∩ previousOnly x = ∅ :=
      Finset.eq_empty_of_forall_notMem fun k member => stayed (carried k member).1
    change 3 * Models.stake _ _ + 2 * scheduled ≤ _
    rw [none]
    simp only [Models.stake, Finset.sum_empty, Nat.mul_zero, Nat.zero_add]
    omega

end

/-- Distinct fresh tags turn the selected payments into an injection into the calls. -/
theorem selected_injection {selected : List SelectedCharge}
    {payments : List (Payment preset)} {paidTags consumed final : List TaggedEntry}
    {calls : List (IndexedDepartureCall preset config)}
    (fresh : FreshTags (config := config) (consumed ++ final) calls)
    (paid : paidTags.Sublist consumed)
    (chosen : SelectedPayments selected payments paidTags) :
    ∃ f : Fin selected.length → Fin calls.length, Function.Injective f ∧ ∀ i,
      (calls[f i]).index = some selected[i].index ∧
      (calls[f i]).call.amount.toNat = selected[i].amount ∧
      (calls[f i]).call.epoch.toNat = selected[i].epoch := by
  have pick : ∀ i : Fin selected.length, ∃ n : Fin calls.length, ∃ tag,
      paidTags[i.val]? = some tag ∧ tag.tag = .fresh n.val ∧
      (calls[n]).index = some selected[i].index ∧
      (calls[n]).call.amount.toNat = selected[i].amount ∧
      (calls[n]).call.epoch.toNat = selected[i].epoch := by
    intro i
    obtain ⟨p, tag, _, found, _, ⟨n, tagged⟩, source, _, index, amount, epoch, _⟩ :=
      chosen.2.2 i
    have member : tag ∈ consumed ++ final := by
      obtain ⟨inside, rfl⟩ := List.getElem?_eq_some_iff.mp found
      exact List.mem_append_left _ (paid.subset (List.getElem_mem inside))
    obtain ⟨called, located, calledIndex, calledAmount, calledEpoch⟩ :=
      fresh.2 tag member n tagged
    obtain ⟨inside, rfl⟩ := List.getElem?_eq_some_iff.mp located
    refine ⟨⟨n, inside⟩, tag, found, tagged, ?_, ?_, ?_⟩
    · simp only [Fin.getElem_fin] at index ⊢
      rw [calledIndex, source, index]
    · simp only [Fin.getElem_fin] at amount ⊢
      rw [calledAmount, amount]
    · simp only [Fin.getElem_fin] at epoch ⊢
      rw [calledEpoch, epoch]
  choose f tag found tagged facts using pick
  refine ⟨f, fun i j same => ?_, fun i => facts i⟩
  have nodup : (paidTags.map (·.tag)).Nodup :=
    fresh.1.sublist ((paid.trans (List.sublist_append_left _ _)).map _)
  obtain ⟨insideI, valueI⟩ := List.getElem?_eq_some_iff.mp (found i)
  obtain ⟨insideJ, valueJ⟩ := List.getElem?_eq_some_iff.mp (found j)
  have equal : (paidTags.map (·.tag))[i.val]'(by simpa using insideI) =
      (paidTags.map (·.tag))[j.val]'(by simpa using insideJ) := by
    simp only [List.getElem_map, valueI, valueJ, tagged i, tagged j, same]
  exact Fin.ext ((List.Nodup.getElem_inj_iff nodup).mp equal)

/-- A paying source waited the delay since its assigned epoch, and pays by the visible end. -/
theorem selected_cutoff {x y : ForkedBeaconState preset} {high : Nat}
    {selected : List SelectedCharge} {payments : List (Payment preset)}
    {tags : List TaggedEntry}
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (chosen : SelectedPayments selected payments tags)
    (delayed : ∀ (i : Fin payments.length) tag v, tags[i.val]? = some tag →
      payments[i].before.state.validators.data[payments[i].source]? = some v →
      tag.epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ v.withdrawableEpoch.toNat)
    (paidBy : ∀ p ∈ payments, p.epoch ≤ (getCurrentEpoch y.state).toNat) :
    Cutoff (config := config) x high selected := by
  intro c member
  obtain ⟨i, inside, rfl⟩ := List.mem_iff_getElem.mp member
  obtain ⟨p, tag, located, found, paying, _, _, _, _, _, epoch, paidAt⟩ :=
    chosen.2.2 ⟨i, inside⟩
  obtain ⟨insideP, rfl⟩ := List.getElem?_eq_some_iff.mp located
  obtain ⟨v, source, _, due, _⟩ := paying
  have wait := delayed ⟨i, insideP⟩ tag v found source
  have last := paidBy _ (List.getElem_mem insideP)
  simp only [Fin.getElem_fin] at epoch paidAt wait last due ⊢
  have bound : horizonEnd x high = (getCurrentEpoch x.state).toNat + driftHorizon x high + 1 := rfl
  unfold driftHorizon at bound
  omega

/-- The epochs of a range from a lower end. -/
private theorem range_filter_length (n m : Nat) :
    ((List.range n).filter (m ≤ ·)).length = n - m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases low : m ≤ n
    · simp [low]; omega
    · simp [low]; omega

/-- Take the injected selected charges.

Each completes by the end of the window less the withdrawal delay.

They fit the initial carry plus the moved flow. -/
theorem selected_capacity {x : ForkedBeaconState preset} {high : Nat}
    (electra : .pectra ≤ x.fork) {selected : List SelectedCharge}
    {calls : List (IndexedDepartureCall preset config)} {epoch : Epoch} {left : Gwei}
    (trace : DepartureQueueTrace (x.state.earliestConsolidationEpoch electra)
      (x.state.consolidationBalanceToConsume electra) (calls.map (·.call)) epoch left)
    (firsts : DepartureCallsFrom (getCurrentEpoch x.state).toNat calls)
    (rates : ∀ called ∈ calls, called.call.rate.toNat ≤
          consolidationFlowAt (config := config) x high 0)
    (injection : ∃ f : Fin selected.length → Fin calls.length, Function.Injective f ∧ ∀ i,
      (calls[f i]).index = some selected[i].index ∧
      (calls[f i]).call.amount.toNat = selected[i].amount ∧
      (calls[f i]).call.epoch.toNat = selected[i].epoch)
    (cutoff : Cutoff (config := config) x high selected) :
    SelectedCapacity (config := config) x high selected := by
  unfold SelectedCapacity
  let delay := config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  by_cases late : horizonEnd x high < delay
  · -- No selected charge can complete and pay by the visible end.
    have empty : selected = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro c member
      have := cutoff c member
      omega
    simp [empty]
  have within : delay ≤ horizonEnd x high := Nat.le_of_not_lt late
  let K := horizonEnd x high - delay
  obtain ⟨f, injective, facts⟩ := injection
  let guarded := fun called : IndexedDepartureCall preset config =>
    if called.call.epoch.toNat ≤ K then called.call.amount.toNat else 0
  -- The selected amounts are the amounts of distinct calls completing by `K`.
  have selectedSum : (selected.map (·.amount)).sum ≤ (calls.map guarded).sum := by
    rw [← Fin.sum_univ_fun_getElem selected (·.amount),
      ← Fin.sum_univ_fun_getElem calls guarded]
    calc
      ∑ i : Fin selected.length, selected[i.val].amount =
          ∑ i : Fin selected.length, (calls[f i]).call.amount.toNat :=
        Finset.sum_congr rfl fun i _ => ((facts i).2.1).symm
      _ = ∑ j ∈ Finset.univ.image f, (calls[j]).call.amount.toNat := by
        rw [Finset.sum_image fun a _ b _ same => injective same]
      _ = ∑ j ∈ Finset.univ.image f, guarded calls[j] := by
        refine Finset.sum_congr rfl fun j member => ?_
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
        have due := cutoff _ (List.getElem_mem i.isLt)
        have epochEq := (facts i).2.2
        simp only [Fin.getElem_fin] at epochEq ⊢
        have early : (calls[(f i).val]).call.epoch.toNat ≤ K := by
          simp only [K]
          omega
        simp only [guarded, early, ↓reduceIte]
      _ ≤ ∑ j : Fin calls.length, guarded calls[j] :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
  have window : (((calls.map (·.call)).filter fun call => call.epoch.toNat ≤ K).map
        fun call => call.amount.toNat).sum ≤
      (if (x.state.earliestConsolidationEpoch electra).toNat ≤ K then
        (x.state.consolidationBalanceToConsume electra).toNat else 0) +
        (K + 1 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestConsolidationEpoch electra).toNat) *
          consolidationFlowAt (config := config) x high 0 := by
    have envelope :=
        trace_window_envelope_from trace (fun _ => consolidationFlowAt (config := config) x high 0)
      (getCurrentEpoch x.state).toNat K
      (fun call member => by
        obtain ⟨called, inside, rfl⟩ := List.mem_map.mp member
        exact firsts called inside)
      (fun call member _ _ _ _ => by
        obtain ⟨called, inside, rfl⟩ := List.mem_map.mp member
        exact rates called inside)
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at envelope
    split_ifs at envelope ⊢ with open_
    · refine envelope.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
      omega
    · omega
  have windowSum : (calls.map guarded).sum =
      (((calls.map (·.call)).filter fun call => decide (call.epoch.toNat ≤ K)).map
        fun call => call.amount.toNat).sum := by
    have split := EthLib.Base.sum_map_ite_eq_sum_filter
      (fun call : DepartureQueueCall => call.epoch.toNat ≤ K) (fun call => call.amount.toNat)
      (calls.map (·.call))
    rw [List.map_map] at split
    exact split
  -- The moved flow is constant from Electra.
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  have constant : consolidationFlowAt (config := config) x high =
      fun _ => consolidationFlowAt (config := config) x high 0 := by
    funext t
    simp only [consolidationFlowAt, consolidationFlow, zero, Nat.not_lt_zero, ↓reduceIte]
  have movedEq : consolidationTransfers (config := config) x high =
      (driftHorizon x high + 2 - delay -
            (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)) *
        consolidationFlowAt (config := config) x high 0 := by
    unfold consolidationTransfers
    rw [zero, constant, List.map_const', List.sum_replicate, smul_eq_mul]
    simp only [Nat.max_zero]
    rw [range_filter_length]
  have carryEq : dueConsolidationCarry (config := config) x high =
      if (x.state.earliestConsolidationEpoch electra).toNat ≤ K then
        (x.state.consolidationBalanceToConsume electra).toNat else 0 := by
    unfold dueConsolidationCarry consolidationBalanceCarry consolidationQueueStart
    simp only [electra, ↓reduceDIte]
    by_cases early : (x.state.earliestConsolidationEpoch electra).toNat ≤ K
    · have opened : (x.state.earliestConsolidationEpoch electra).toNat +
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ horizonEnd x high := by
        simp only [K] at early
        omega
      simp only [opened, early, ↓reduceIte]
    · have closed : ¬ (x.state.earliestConsolidationEpoch electra).toNat +
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ horizonEnd x high := by
        simp only [K] at early
        omega
      simp only [closed, early, ↓reduceIte]
  have start : consolidationQueueStart x = (x.state.earliestConsolidationEpoch electra).toNat := by
    simp [consolidationQueueStart, electra]
  have flow : K + 1 - max (getCurrentEpoch x.state).toNat
      (x.state.earliestConsolidationEpoch electra).toNat ≤
      driftHorizon x high + 2 - delay -
        ((x.state.earliestConsolidationEpoch electra).toNat - (getCurrentEpoch x.state).toNat) := by
    have bound : horizonEnd x high = (getCurrentEpoch x.state).toNat + driftHorizon x high + 1 :=
        rfl
    simp only [K]
    omega
  calc (selected.map (·.amount)).sum ≤ (calls.map guarded).sum := selectedSum
    _ = _ := windowSum
    _ ≤ _ := window
    _ ≤ dueConsolidationCarry (config := config) x high +
        consolidationTransfers (config := config) x high := by
      rw [movedEq, carryEq, start]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ flow) _

/-- A tagged pass is determined by its epoch, state and queue. -/
theorem TaggedPass.unique {fork : Fork} {next : Epoch} {s t t' : BeaconState preset fork}
    {queue suffix suffix' consumed consumed' : List TaggedEntry}
    {paid paid' : List (TaggedEntry × Payment preset)}
    (one : TaggedPass next s queue t suffix consumed paid)
    (two : TaggedPass next s queue t' suffix' consumed' paid') :
    t = t' ∧ suffix = suffix' ∧ consumed = consumed' ∧ paid = paid' := by
  induction one generalizing t' suffix' consumed' paid' with
  | nil =>
    cases two
    exact ⟨rfl, rfl, rfl, rfl⟩
  | waiting found unslashed later =>
    cases two with
    | waiting => exact ⟨rfl, rfl, rfl, rfl⟩
    | slashed found' slashed' _ =>
      cases found.symm.trans found'
      rw [slashed'] at unslashed
      cases unslashed
    | paid found' _ due _ _ _ _ =>
      cases found.symm.trans found'
      have lower := UInt64.lt_iff_toNat_lt.mp later
      have upper := UInt64.le_iff_toNat_le.mp due
      omega
  | slashed found slashed _ ih =>
    cases two with
    | waiting found' unslashed' _ =>
      cases found.symm.trans found'
      rw [slashed] at unslashed'
      cases unslashed'
    | slashed _ _ rest' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih rest'
      exact ⟨rfl, rfl, rfl, rfl⟩
    | paid found' unslashed' _ _ _ _ _ =>
      cases found.symm.trans found'
      rw [slashed] at unslashed'
      cases unslashed'
  | paid found unslashed due balance debited credited _ ih =>
    cases two with
    | waiting found' _ later' =>
      cases found.symm.trans found'
      have lower := UInt64.lt_iff_toNat_lt.mp later'
      have upper := UInt64.le_iff_toNat_le.mp due
      omega
    | slashed found' slashed' _ =>
      cases found.symm.trans found'
      rw [slashed'] at unslashed
      cases unslashed
    | paid found' _ _ balance' debited' credited' rest' =>
      cases found.symm.trans found'
      cases balance.symm.trans balance'
      cases debited.symm.trans debited'
      cases credited.symm.trans credited'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih rest'
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- Calls with the same index, queue call and entry are equal. -/
private theorem IndexedDepartureCall.ext_fields {a b : IndexedDepartureCall preset config}
    (index : a.index = b.index) (earliest : a.call.earliest = b.call.earliest)
    (available : a.call.available = b.call.available) (first : a.call.first = b.call.first)
    (rate : a.call.rate = b.call.rate) (amount : a.call.amount = b.call.amount)
    (epoch : a.call.epoch = b.call.epoch) (left : a.call.left = b.call.left)
    (entry : a.entry = b.entry) : a = b := by
  obtain ⟨ai, ⟨ae, aa, af, ar, am, ap, al, _⟩, an, _, _⟩ := a
  obtain ⟨bi, ⟨be, ba, bf, br, bm, bp, bl, _⟩, bn, _, _⟩ := b
  simp only at index earliest available first rate amount epoch left entry
  subst index earliest available first rate amount epoch left entry
  rfl

/-- An appended queue is longer than its prefix. -/
private theorem queueErasure_append_ne {before : List TaggedEntry} {extra : TaggedEntry}
    {actual : List PendingConsolidation}
    (kept : QueueErasure before actual) (grown : QueueErasure (before ++ [extra]) actual) :
    False := by
  unfold QueueErasure at kept grown
  have lengths := congrArg List.length (kept.trans grown.symm)
  simp at lengths

/-- A tagged event is determined by its event, position and input queue. -/
theorem TagEvent.unique {e : BalanceEvent preset} {position : Nat}
    {before after after' consumed consumed' : List TaggedEntry}
    {paid paid' : List (TaggedEntry × Payment preset)}
    {calls calls' : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed paid calls)
    (two : TagEvent (config := config) e position before after' consumed' paid' calls') :
    after = after' ∧ consumed = consumed' ∧ paid = paid' ∧ calls = calls' := by
  obtain ⟨_, erasure, branch⟩ := one
  obtain ⟨_, erasure', branch'⟩ := two
  rcases branch with ⟨other, rfl, rfl, rfl, rfl⟩ |
      ⟨fork, s, t, electra, _, sourceIndex, source, targetIndex, called, excess, atBefore,
        atAfter, _, found, queued, index, amount, earliest, available, epoch, left, first, rate,
        rfl, rfl, rfl, rfl⟩ |
      ⟨fork, s, t, u, electra, next, consolidations, atBefore, atAfter, nextOk, _, pass, _, _,
        rfl⟩ <;>
    rcases branch' with ⟨other', rfl, rfl, rfl, rfl⟩ |
      ⟨fork', s', t', electra', _, sourceIndex', source', targetIndex', called', excess',
        atBefore', atAfter', _, found', queued', index', amount', earliest', available', epoch',
        left', first', rate', rfl, rfl, rfl, rfl⟩ |
      ⟨fork', s', t', u', electra', next', consolidations', atBefore', atAfter', nextOk', _,
        pass', _, _, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact (queueErasure_append_ne erasure erasure').elim
  · exact absurd consolidations' other
  · exact (queueErasure_append_ne erasure' erasure).elim
  · cases atBefore.symm.trans atBefore'
    cases atAfter.symm.trans atAfter'
    have entries := erasure.trans erasure'.symm
    simp only [List.map_append, List.map_cons, List.map_nil,
      List.append_cancel_left_eq, List.cons.injEq, and_true, PendingConsolidation.mk.injEq]
      at entries
    obtain ⟨rfl, rfl⟩ := entries
    cases found.symm.trans found'
    have entryNone : ∀ c : IndexedDepartureCall preset config,
        c.index = some sourceIndex.toNat → c.entry = none := by
      intro c some
      cases hc : c.entry with
      | none => rfl
      | some pending =>
        have := c.tagged.mpr (by simp [hc])
        rw [some] at this
        cases this
    have same : called = called' := IndexedDepartureCall.ext_fields (index.trans index'.symm)
      (earliest.trans earliest'.symm) (available.trans available'.symm)
      (Except.ok.inj (first.symm.trans first')) (Except.ok.inj (rate.symm.trans rate'))
      (amount.trans amount'.symm) (epoch.trans epoch'.symm) (left.trans left'.symm)
      ((entryNone called index).trans (entryNone called' index').symm)
    subst same
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [excess] at consolidations'
    cases consolidations'
  · exact absurd consolidations other'
  · rw [excess'] at consolidations
    cases consolidations
  · cases atBefore.symm.trans atBefore'
    cases atAfter.symm.trans atAfter'
    cases Except.ok.inj (nextOk.symm.trans nextOk')
    obtain ⟨rfl, rfl, rfl, rfl⟩ := TaggedPass.unique pass pass'
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A tag replay is determined by its events, start position and initial queue. -/
theorem TagReplay.unique {position : Nat} {events : List (BalanceEvent preset)}
    {initial final final' consumed consumed' : List TaggedEntry}
    {paid paid' : List (TaggedEntry × Payment preset)}
    {calls calls' : List (IndexedDepartureCall preset config)}
    (one : TagReplay (config := config) position events initial final consumed paid calls)
    (two : TagReplay (config := config) position events initial final' consumed' paid' calls') :
    final = final' ∧ consumed = consumed' ∧ paid = paid' ∧ calls = calls' := by
  induction one generalizing final' consumed' paid' calls' with
  | nil =>
    cases two
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons event _ ih =>
    cases two with
    | cons event' rest' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := TagEvent.unique event event'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih rest'
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- The derived drift bound follows from the state bound at every prefix of the tail.

The bound is the a priori drift at `x`, a constant, so it grows trivially.

Each in-horizon prefix is supported.

It ends before Gloas because the rest of the tail follows it. -/
theorem derivedProducer_of_state {g x y : ForkedBeaconState preset}
    (state : ∀ {u : ForkedBeaconState preset},
      StateProducer (config := config) (checks := checks) (g := g) (x := x) (y := u)) :
    DerivedProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail genesis parameters caps aligned twoSlots early high startEpoch guard
  exact derivedDrift_le_of_prefixes high startEpoch (fun _ => drift (config := config) x high)
    (fun _ _ _ => Nat.le_refl _)
    (fun pre post within => state shared pre high
      ⟨genesis, parameters, caps, aligned,
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early, within, guard⟩
      twoSlots)
    tail

section

open Cryptography.Bls

/-- The tags of a queue name its entries in order. -/
theorem initialTags_entries (queue : List PendingConsolidation) :
    (initialTags queue).map (·.entry) = queue := by
  simp [initialTags, List.map_map, Function.comp_def, List.zipIdx_map_fst]

/-- The window starts with its initial ownership and a reserved frame at `x`.

The frame tags the actual pending queue at `x`, one initial tag per entry.

No initial tag is fresh, so the assignment cut holds for any rounding.

The initial ownership covers the endpoint and the future effective balances at `x`. -/
theorem reservedFrame_initial {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (high : Nat) (electraX : .pectra ≤ x.fork)
    (rounding : Nat → Nat) :
    ∃ owned : Ownership, OwnedInitial x high owned ∧
      ReservedFrame (config := config) (checks := checks) x high rounding x x
        (getCurrentEpoch x.state) (getCurrentEpoch x.state)
        (initialTags (x.state.pendingConsolidations electraX).data.toList) owned owned ∧
      EndpointCoverAll x x owned ∧ FutureEffectiveCover x x owned := by
  obtain ⟨_, rfl, initial, reserve⟩ := initialOwnership_exists shared genesis early high
  have queueEq : pendingQueue x = (x.state.pendingConsolidations electraX).data.toList := by
    simp only [pendingQueue, electraX, ↓reduceDIte]
  have erasure : QueueErasure (initialTags (x.state.pendingConsolidations electraX).data.toList)
      (pendingQueue x) := by
    rw [QueueErasure, initialTags_entries, queueEq]
  -- An initial tag is never fresh.
  have assignment : AssignmentCut rounding
      (initialTags (x.state.pendingConsolidations electraX).data.toList)
      (initialOwnership x high) := by
    intro tag member position fresh
    simp only [initialTags, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    cases fresh
  refine ⟨_, initial, reservedFrame_refl ?_ assignment erasure,
    initialOwnership_endpointCover shared genesis early high, initialOwnership_futureCover x high⟩
  rw [initialTags_entries, ← queueEq]
  exact reserve

end

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
