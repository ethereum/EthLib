module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoad
public import EthLib.Consensus.Proofs.Transition.Upgrade

/-!
# Proofs: the upgrades raise the validators plus the pending deposits only at Electra

An upgrade between forks keeps the size of the registry.

Only the upgrades to Electra and to Gloas change the pending deposits.

The upgrade to Electra creates the queue of pending deposits.

Each validator not yet active then waits as a pending deposit of its whole balance.

Its balance becomes zero, so it has no balance above the activation balance to queue too.

Each other validator with compounding credentials queues at most one deposit of its excess.

[EIP-7251] introduces the pending deposits and the compounding credentials.

So each validator adds at most one pending deposit.

Before Electra the count is the size of the registry alone, so the upgrade at most doubles it.

The upgrade to Gloas moves the pending deposits of builders to the builders, or drops them.

[EIP-8282] keeps that onboarding at the fork.

That only removes pending deposits, and the upgrade to Heze carries the queue over unchanged.

So a slot across forks raises the count only when it crosses Electra, and then at most doubles it.

Before Electra the count is the size of the registry, so the rise is at most that size.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#fork-transition-onboarding
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The number of positions in a range whose balance is above the activation balance. -/
private def excessCount (preset : Preset) (count : Nat) (balances : Array Gwei) : Nat :=
  (List.range count).countP fun j => preset.MIN_ACTIVATION_BALANCE < balances[j]?.getD 0

/-- A predicate that drops one member of a list and agrees elsewhere counts at least one fewer. -/
private theorem countP_add_one_le {l : List Nat} {p q : Nat → Bool} {k : Nat} (mem : k ∈ l)
    (was : p k = true) (gone : q k = false) (same : ∀ j, j ≠ k → q j = p j) :
    l.countP q + 1 ≤ l.countP p := by
  induction l with
  | nil => cases mem
  | cons head tail ih =>
    by_cases at_head : head = k
    · subst at_head
      have mono : tail.countP q ≤ tail.countP p := List.countP_mono_left fun j _ holds => by
        by_cases here : j = head
        · subst here
          simp_all
        · rwa [← same j here]
      simp only [List.countP_cons, was, gone, ite_true, Bool.false_eq_true, ite_false]
      omega
    · have inTail := (List.mem_cons.mp mem).resolve_left (Ne.symm at_head)
      have := ih inTail
      rw [List.countP_cons, List.countP_cons, same head at_head]
      split <;> omega

/-- The index of a validator that a read finds lies within the registry. -/
private theorem lt_of_getValidator {fork : Fork} {state : BeaconState preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator) :
    index.toNat < state.validators.data.size := by
  unfold getValidator at found
  split at found
  · rename_i read
    exact (Array.getElem?_eq_some_iff.mp read).1
  · cases found

/-- A balance that a read finds sits at its index. -/
private theorem getElem?_of_getBalance {fork : Fork} {state : BeaconState preset fork}
    {index : ValidatorIndex} {balance : Gwei}
    (found : getBalance state index = .ok balance) :
    state.balances.data[index.toNat]? = some balance := by
  unfold getBalance at found
  split at found
  · rename_i read
    cases found
    exact read
  · cases found

/-- Lowering one balance to the activation balance from above lowers the count by one. -/
private theorem excessCount_set {count k : Nat} {balances : Array Gwei} {balance : Gwei}
    (inside : k < balances.size) (inRange : k < count) (read : balances[k]? = some balance)
    (above : preset.MIN_ACTIVATION_BALANCE < balance) :
    excessCount preset count (balances.set k preset.MIN_ACTIVATION_BALANCE inside) + 1 ≤
      excessCount preset count balances := by
  unfold excessCount
  refine countP_add_one_le (List.mem_range.mpr inRange) ?_ ?_ ?_
  · simp [read, above]
  · simp
  · intro j other
    simp [Ne.symm other]

/-- Queueing a validator not yet active adds one deposit and keeps the registry size.

Only its balance becomes zero. -/
private theorem queuePreActivation_load {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    (after.pendingDeposits electra).data.size = (state.pendingDeposits electra).data.size + 1 ∧
      after.validators.data.size = state.validators.data.size ∧
      ∀ j, after.balances.data[j]? =
        if j = index.toNat then some 0 else state.balances.data[j]? := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, -, _, -, _, appended, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨inside₁, rfl⟩ := setBalance_ok set₁
  obtain ⟨inside₂, rfl⟩ := setValidator_ok set₂
  refine ⟨by simp [appendWithinLimit_data appended],
    (sameSizes_putValidator _ inside₂ _).1, fun j => ?_⟩
  simp only [BeaconState.putValidator, BeaconState.putBalance, Array.getElem?_set]
  split <;> simp_all [eq_comm]

/-- The queueing of the validators not yet active adds one deposit for each.

It keeps the registry size, and leaves each queued balance at zero. -/
private theorem foldlM_queuePreActivation_load {fork : Fork} {electra : .pectra ≤ fork} :
    ∀ (indices : List ValidatorIndex) {state after : BeaconState preset fork},
      indices.foldlM (fun state index => queuePreActivation state electra index) state =
          .ok after →
        (after.pendingDeposits electra).data.size =
            (state.pendingDeposits electra).data.size + indices.length ∧
          after.validators.data.size = state.validators.data.size ∧
          (∀ j : Nat, state.balances.data[j]? = some 0 → after.balances.data[j]? = some 0) ∧
          ∀ index ∈ indices, after.balances.data[index.toNat]? = some 0 := by
  intro indices
  induction indices with
  | nil =>
    intro state after computed
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | cons head rest ih =>
    intro state after computed
    rw [List.foldlM_cons] at computed
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨pending, sized, balances⟩ := queuePreActivation_load first
    obtain ⟨pending', sized', kept, zeroed⟩ := ih tail
    refine ⟨by simp only [List.length_cons]; omega, sized'.trans sized, fun j zero => ?_,
      fun index mem => ?_⟩
    · apply kept
      rw [balances j]
      split <;> simp_all
    · rcases List.mem_cons.mp mem with rfl | inRest
      · apply kept
        simp [balances]
      · exact zeroed index inRest

/-- Queueing one excess balance keeps the registry size.

It never raises the pending deposits plus the balances above the activation balance. -/
private theorem queueCompoundingExcess_load {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index count : Nat} (sized : state.validators.data.size = count)
    (computed : queueCompoundingExcess state electra index = .ok after) :
    after.validators.data.size = count ∧
      (after.pendingDeposits electra).data.size + excessCount preset count after.balances.data ≤
        (state.pendingDeposits electra).data.size +
          excessCount preset count state.balances.data := by
  have sizes := (electraKept_queueCompoundingExcess computed).1.1
  refine ⟨sizes.trans sized, ?_⟩
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨balance, found, queued⟩ := queued
      split at queued
      · rename_i above
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, validatorFound, _, appended, _, set, rfl⟩ := queued
        obtain ⟨inside, rfl⟩ := setBalance_ok set
        have within := lt_of_getValidator validatorFound
        have read := getElem?_of_getBalance found
        have fewer := excessCount_set (preset := preset) inside (sized ▸ within) read above
        simp only [BeaconState.putBalance, appendWithinLimit_data appended, Array.size_push]
        omega
      · cases queued
        exact Nat.le_refl _
    · cases computed
      exact Nat.le_refl _
  · cases computed
    exact Nat.le_refl _

/-- The queueing of the excess balances never raises the pending deposits.

This holds once the balances above the activation balance are added to them. -/
private theorem foldlM_queueCompoundingExcess_load {fork : Fork} {electra : .pectra ≤ fork}
    {count : Nat} :
    ∀ (indices : List Nat) {state after : BeaconState preset fork},
      state.validators.data.size = count →
      indices.foldlM (fun state index => queueCompoundingExcess state electra index) state =
          .ok after →
        (after.pendingDeposits electra).data.size +
            excessCount preset count after.balances.data ≤
          (state.pendingDeposits electra).data.size +
            excessCount preset count state.balances.data := by
  intro indices
  induction indices with
  | nil =>
    intro state after _ computed
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Nat.le_refl _
  | cons head rest ih =>
    intro state after sized computed
    rw [List.foldlM_cons] at computed
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨sized', step⟩ := queueCompoundingExcess_load sized first
    exact Nat.le_trans (ih sized' tail) step

/-- The positions of some indexed entries of a list, once sorted, are distinct and in range. -/
private theorem sortedPositions_nodup {α : Type} {xs : List α} (small : xs.length < 2 ^ 64)
    {l : List (α × Nat)} (sub : l.Sublist xs.zipIdx) {le : α × Nat → α × Nat → Bool} :
    (((l.mergeSort le).map fun x => x.2.toUInt64).map UInt64.toNat).Nodup ∧
      ∀ j ∈ ((l.mergeSort le).map fun x => x.2.toUInt64).map UInt64.toNat, j < xs.length := by
  have perm := List.mergeSort_perm l le
  have inside : ∀ x ∈ l.mergeSort le, x.2 < xs.length := fun x mem => by
    have := List.snd_lt_of_mem_zipIdx (sub.subset (perm.subset mem))
    omega
  have positions : ((l.mergeSort le).map fun x => x.2.toUInt64).map UInt64.toNat =
      (l.mergeSort le).map Prod.snd := by
    rw [List.map_map]
    refine List.map_congr_left fun x mem => ?_
    have := inside x mem
    simp only [Function.comp_apply, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [positions]
  refine ⟨(perm.map Prod.snd).nodup_iff.mpr
    (List.Nodup.sublist (sub.map _) ?_), fun j mem => ?_⟩
  · rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  · obtain ⟨x, found, rfl⟩ := List.mem_map.mp mem
    exact inside x found

/-- The validators not yet active are distinct positions of the registry. -/
private theorem preActivationIndices_nodup {fork : Fork} (state : BeaconState preset fork)
    (small : state.validators.data.size < 2 ^ 64) :
    ((preActivationIndices state).map UInt64.toNat).Nodup ∧
      ∀ j ∈ (preActivationIndices state).map UInt64.toNat, j < state.validators.data.size := by
  unfold preActivationIndices
  dsimp only
  rw [← Array.length_toList]
  exact sortedPositions_nodup (by rwa [Array.length_toList]) List.filter_sublist

/-- Zero balances at distinct positions of a range leave only the other positions to count. -/
private theorem excessCount_le {count : Nat} {balances : Array Gwei} {zeroed : List Nat}
    (distinct : zeroed.Nodup) (inside : ∀ j ∈ zeroed, j < count)
    (zero : ∀ j ∈ zeroed, balances[j]? = some 0) :
    excessCount preset count balances + zeroed.length ≤ count := by
  have sub : zeroed.Subperm (List.range count) :=
    List.subperm_of_subset distinct fun j mem => List.mem_range.mpr (inside j mem)
  have covered : zeroed.length ≤ (List.range count).countP (fun j => decide (j ∈ zeroed)) := by
    have := sub.countP_le (fun j => decide (j ∈ zeroed))
    rwa [List.countP_eq_length.mpr (by simp)] at this
  have rest : excessCount preset count balances ≤
      (List.range count).countP (fun j => !decide (j ∈ zeroed)) := by
    refine List.countP_mono_left fun j _ above => ?_
    by_cases mem : j ∈ zeroed
    · simp [zero j mem] at above
    · simp [mem]
  have split := List.length_eq_countP_add_countP (fun j => decide (j ∈ zeroed))
    (l := List.range count)
  simp only [List.length_range, decide_not, decide_eq_true_eq] at split rest
  omega

/-- A bound by the count stays a bound when the count is kept or doubled. -/
private theorem le_ite_mul {a b : Nat} (P : Prop) [Decidable P] (le : a ≤ b) :
    a ≤ (if P then 2 else 1) * b := by
  split <;> omega

/-- The onboarding keeps at most one pending deposit for each that it reads. -/
private theorem foldlM_onboardDeposit_size {validatorKeys : List Cryptography.Bls.BLSPubkey} :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset .glamsterdam}
      {kept kept' : Array PendingDeposit},
      deposits.foldlM (onboardDeposit config checks validatorKeys) (state, kept) =
          .ok (after, kept') →
      kept'.size ≤ kept.size + deposits.length := by
  intro deposits
  induction deposits with
  | nil =>
    intro state after kept kept' folded
    cases folded
    exact Nat.le_refl _
  | cons deposit rest ih =>
    intro state after kept kept' folded
    rw [List.foldlM_cons] at folded
    obtain ⟨⟨middle, middleKept⟩, step, folded⟩ := bind_ok_iff.mp folded
    have bound := ih folded
    rcases onboardDeposit_cases step with ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl, -⟩
    · simp only [Array.size_push, List.length_cons] at bound ⊢
      omega
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

/-- The onboarding of builders never raises the validators plus the pending deposits. -/
private theorem onboardBuilders_registryLoad_le {state after : BeaconState preset .glamsterdam}
    (computed : onboardBuildersFromPendingDeposits config checks state = .ok after) :
    registryLoad after ≤ registryLoad state := by
  unfold onboardBuildersFromPendingDeposits at computed
  obtain ⟨⟨folded, kept⟩, foldedOk, rest⟩ := bind_ok_iff.mp computed
  cases rest
  rw [← Array.foldlM_toList] at foldedOk
  have bound := foldlM_onboardDeposit_size foldedOk
  obtain ⟨⟨builders, rfl⟩, -⟩ := foldlM_onboardDeposit foldedOk
  clear computed foldedOk
  simp only [registryLoad, Array.length_toList, Array.size_empty] at bound ⊢
  rw [dite_eq_left (by decide), dite_eq_left (by decide)]
  omega

/-- The upgrade to Electra adds at most one pending deposit for each validator. -/
theorem upgradeToElectra_registryLoad_le {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    registryLoad after ≤ registryLoad pre + pre.validators.data.size := by
  have sizes := (upgradeToElectra_spec computed).1
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  have small : pre.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (pre.validators.bound (by decide)) (UInt64.toNat_lt _)
  obtain ⟨added, sized, -, zeroed⟩ := foldlM_queuePreActivation_load _ queued
  obtain ⟨distinct, inside⟩ := preActivationIndices_nodup _ small
  have fewer := excessCount_le (preset := preset) distinct inside fun j mem => by
    obtain ⟨index, found, rfl⟩ := List.mem_map.mp mem
    exact zeroed index found
  have queuedExcess := foldlM_queueCompoundingExcess_load _ rfl compounded
  have sized' : middle.validators.data.size = pre.validators.data.size := sized
  rw [sized'] at queuedExcess
  rw [List.length_map] at fewer
  obtain ⟨queued, queuedSize, rest⟩ : ∃ queued : Nat,
      (middle.pendingDeposits (by decide)).data.size = queued ∧
        excessCount preset pre.validators.data.size middle.balances.data + queued ≤
          pre.validators.data.size :=
    ⟨_, added.trans (Nat.zero_add _), fewer⟩
  clear added fewer zeroed inside distinct compounded
  unfold registryLoad
  rw [dite_eq_left (by decide), dite_eq_right (by decide), sizes]
  omega

/-- The upgrade to Gloas never raises the validators plus the pending deposits. -/
theorem upgradeToGloas_registryLoad_le {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok after) :
    registryLoad after ≤ registryLoad pre := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  refine Nat.le_trans (onboardBuilders_registryLoad_le onboarded) (Nat.le_of_eq ?_)
  unfold registryLoad
  rw [dite_eq_left (by decide), dite_eq_left (by decide)]
  rfl

/-- The upgrade to Heze never raises the validators plus the pending deposits. -/
theorem upgradeToHeze_registryLoad_le {pre : BeaconState preset .glamsterdam}
    {after : BeaconState preset .hegota} (computed : upgradeToHeze config pre = .ok after) :
    registryLoad after ≤ registryLoad pre := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  unfold registryLoad
  rw [dite_eq_left (by decide), dite_eq_left (by decide)]
  exact Nat.le_refl _

/-- One upgrade at most doubles the count when it leads to Electra.

It never raises the count otherwise. -/
private theorem upgradeNext_registryLoad_le_double {pre : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok next) :
    registryLoad next.val.state ≤
      (if pre.fork < .pectra ∧ .pectra ≤ next.val.fork then 2 else 1) * registryLoad pre.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    refine le_ite_mul _ (Nat.le_of_eq ?_)
    unfold registryLoad
    rw [dite_eq_right (by dsimp only; decide), dite_eq_right (by dsimp only; decide),
      (upgradeToAltair_spec upgraded).1]
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    refine le_ite_mul _ (Nat.le_of_eq ?_)
    unfold registryLoad
    rw [dite_eq_right (by dsimp only; decide), dite_eq_right (by dsimp only; decide)]
    rfl
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    have doubled := upgradeToElectra_registryLoad_le upgraded
    have registry : state.validators.data.size ≤ registryLoad state := Nat.le_add_right _ _
    rw [ite_eq_left ⟨by dsimp only; decide, by dsimp only; decide⟩]
    dsimp only
    omega
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    refine le_ite_mul _ (Nat.le_of_eq ?_)
    simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    unfold registryLoad
    rw [dite_eq_left (by dsimp only; decide), dite_eq_left (by dsimp only; decide)]
    rfl
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact le_ite_mul _ (upgradeToGloas_registryLoad_le upgraded)
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact le_ite_mul _ (upgradeToHeze_registryLoad_le upgraded)
  all_goals simp only [upgradeNext] at computed; cases computed

/-- The upgrades due at a slot at most double the count when they cross Electra.

They never raise it otherwise. -/
private theorem processUpgrades_registryLoad_le_double {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    registryLoad after.state ≤
      (if forked.fork < .pectra ∧ .pectra ≤ after.fork then 2 else 1) *
        registryLoad forked.state := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp computed
    have first := upgradeNext_registryLoad_le_double nextOk
    have second := more next rest
    have later : forked.fork.ctorIdx < next.val.fork.ctorIdx := next.property
    have ordered : next.val.fork.ctorIdx ≤ after.fork.ctorIdx := processUpgrades_fork_le rest
    change registryLoad after.state ≤
      (if forked.fork.ctorIdx < Fork.pectra.ctorIdx ∧ Fork.pectra.ctorIdx ≤ after.fork.ctorIdx
        then 2 else 1) * registryLoad forked.state
    change registryLoad next.val.state ≤
      (if forked.fork.ctorIdx < Fork.pectra.ctorIdx ∧ Fork.pectra.ctorIdx ≤ next.val.fork.ctorIdx
        then 2 else 1) * registryLoad forked.state at first
    change registryLoad after.state ≤
      (if next.val.fork.ctorIdx < Fork.pectra.ctorIdx ∧ Fork.pectra.ctorIdx ≤ after.fork.ctorIdx
        then 2 else 1) * registryLoad next.val.state at second
    split at first <;> split at second <;> split <;> omega
  | case2 forked _ =>
    cases computed
    rw [ite_eq_right fun both => absurd (Nat.lt_of_lt_of_le both.1 both.2) (Nat.lt_irrefl _)]
    omega

/-- A slot with the upgrades due at it at most doubles the count when it crosses Electra.

It never raises the count otherwise. -/
private theorem advanceSlotAcross_registryLoad_le_double {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    registryLoad after.state ≤
      (if forked.fork < .pectra ∧ .pectra ≤ after.fork then 2 else 1) *
        registryLoad forked.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp computed
  exact Nat.le_trans (processUpgrades_registryLoad_le_double upgrades)
    (Nat.mul_le_mul_left _ (advanceSlot_registryLoad_le slotOk))


/-- Before Electra, the count is the size of the registry. -/
private theorem registryLoad_of_not_electra {fork : Fork} {state : BeaconState preset fork}
    (early : ¬ .pectra ≤ fork) : registryLoad state = state.validators.data.size := by
  simp [registryLoad, early]

/-- A bound that at most doubles a count of a state before Electra adds at most its registry. -/
private theorem additive_of_double {fork post : Fork} {state : BeaconState preset fork}
    {count : Nat}
    (bound : count ≤ (if fork < .pectra ∧ .pectra ≤ post then 2 else 1) * registryLoad state) :
    count ≤ registryLoad state +
      if fork < .pectra ∧ .pectra ≤ post then state.validators.data.size else 0 := by
  split at bound
  · rename_i crossed
    have early : ¬ Fork.pectra ≤ fork := fun later => absurd (Nat.lt_of_lt_of_le crossed.1 later)
      (Nat.lt_irrefl _)
    rw [ite_eq_left crossed, ← registryLoad_of_not_electra early]
    omega
  · rw [ite_eq_right ‹_›]
    omega

/-- One upgrade adds at most the size of the registry to the count when it leads to Electra.

It never raises the count otherwise. -/
theorem upgradeNext_registryLoad_le {pre : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok next) :
    registryLoad next.val.state ≤ registryLoad pre.state +
      if pre.fork < .pectra ∧ .pectra ≤ next.val.fork then pre.state.validators.data.size
      else 0 :=
  additive_of_double (upgradeNext_registryLoad_le_double computed)

/-- The upgrades due at a slot add at most the size of the registry when they cross Electra.

They never raise the count otherwise. -/
theorem processUpgrades_registryLoad_le {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    registryLoad after.state ≤ registryLoad forked.state +
      if forked.fork < .pectra ∧ .pectra ≤ after.fork then forked.state.validators.data.size
      else 0 :=
  additive_of_double (processUpgrades_registryLoad_le_double computed)

/-- A slot with the upgrades due at it adds at most the registry size when it crosses Electra.

It never raises the count otherwise.

The registry size is that of the state before the slot. -/
theorem advanceSlotAcross_registryLoad_le {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    registryLoad after.state ≤ registryLoad forked.state +
      if forked.fork < .pectra ∧ .pectra ≤ after.fork then forked.state.validators.data.size
      else 0 :=
  additive_of_double (advanceSlotAcross_registryLoad_le_double computed)

end EthLib.Consensus
