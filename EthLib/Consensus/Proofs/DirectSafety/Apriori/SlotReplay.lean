module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Baseline

/-!
# The replay of a slot

A slot step of a shared run keeps the reserved replay, and so does each quiet block operation.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section

open Cryptography.Bls Uint64

/-- A change of BLS credentials to an execution address is quiet.

Neither credential is compounding, so the largest effective balance stays.

Nothing else that a registry step reads changes. -/
private theorem QuietStep.blsChange {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t)
    (ordered : ExitsOrdered s) : QuietStep electra s t := by
  have held := processBlsToExecutionChange_slashed_exit_assigned ok
  obtain ⟨v, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
  have read : s.validators.data[signed.message.validatorIndex.toNat]? = some v :=
    getValidator_eq_ok_iff.mp found
  have old : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = false := by
    rw [bls]
    decide
  have first : (executionCredentials signed.message.toExecutionAddress)[0] =
      ETH1_ADDRESS_WITHDRAWAL_PREFIX[0] := by
    simp [executionCredentials]
  have new : ((executionCredentials signed.message.toExecutionAddress)[0] ==
      COMPOUNDING_WITHDRAWAL_PREFIX[0]) = false := by
    rw [first]
    decide
  -- An opaque name for the new credentials keeps unification from computing them.
  generalize executionCredentials signed.message.toExecutionAddress = credentials at set new
  have cap : withdrawalMaxEffectiveBalance preset fork
        { v with withdrawalCredentials := credentials } =
      withdrawalMaxEffectiveBalance preset fork v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
      hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, old, new]
  have registry := RegistryStep.set read set rfl rfl cap id ⟨fun _ => rfl, fun _ => rfl⟩
    (.inl rfl) (fun _ _ => rfl) (ordered v (Array.mem_of_getElem? read)) ordered
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨registry, rfl, rfl, rfl, rfl, held⟩

/-- The BLS credential changes of a block record nothing. -/
theorem operationReplay_blsChanges (x : ForkedBeaconState preset) (high : Nat)
    (rounding : Nat → Nat) {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} (body : BeaconBlockBody preset fork)
    (ok : processBlsToExecutionChanges config checks s body = .ok t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] := by
  unfold processBlsToExecutionChanges at ok
  split at ok
  · rename_i capella
    have folded : (body.blsToExecutionChanges capella).data.toList.foldlM
        (processBlsToExecutionChange config checks) s = .ok t := by
      simpa only [Array.foldlM_toList] using ok
    exact operationReplay_quiet
      (foldlM_framePath _ _ folded fun _ _ _ _ eq => .credentials eq)
      (foldlM_step (QuietStep electra) (fun _ => .refl) .trans (·.1.2.2.2.2.2.2) (·.1.2.2.2.1) _
        (fun _ _ _ step ordered _ => QuietStep.blsChange step ordered) _ folded)
  · rename_i before
    exact absurd (Nat.le_trans (by decide) electra) before

/-- The run facts of one block step.

The current epoch stays.

The balance match, the order of exits and withdrawals and the lifecycle from `x` carry. -/
theorem runFacts_of_frame {x : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} (frame : BlockFrame a b) (life : RegistryLifecycle a b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) :=
  ⟨by simp only [getCurrentEpoch, frame.slot], fun matched ordered start =>
    ⟨frame.balancesMatch matched, frame.exitsOrdered ordered, start.trans life⟩⟩

theorem runFacts_proposerSlashing {x : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks a slashing = .ok b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) :=
  runFacts_of_frame (frame_processProposerSlashing ok)
    (registryLifecycle_processProposerSlashing ok)

theorem runFacts_attesterSlashing {x : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks a slashing = .ok b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) :=
  runFacts_of_frame (frame_processAttesterSlashing ok)
    (registryLifecycle_processAttesterSlashing ok)

theorem runFacts_voluntaryExits {x : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} {exits : List SignedVoluntaryExit}
    (ok : exits.foldlM (processVoluntaryExit config checks) a = .ok b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) := by
  exact runFacts_of_frame (BlockFrame.foldlM (fun _ _ _ one => frame_processVoluntaryExit one) ok)
    (RegistryLifecycle.foldlM (fun _ _ _ one => registryLifecycle_processVoluntaryExit one) ok)

theorem runFacts_withdrawalRequests {x : ForkedBeaconState preset} {fork : Fork}
    {electra : .pectra ≤ fork} {a b : BeaconState preset fork}
    {requests : List WithdrawalRequest}
    (ok : requests.foldlM (processWithdrawalRequest config · electra ·) a = .ok b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) := by
  exact runFacts_of_frame
      (BlockFrame.foldlM (fun _ _ _ one => frame_processWithdrawalRequest one) ok)
    (RegistryLifecycle.foldlM (fun _ _ _ one => registryLifecycle_processWithdrawalRequest one) ok)

theorem runFacts_blsChanges {x : ForkedBeaconState preset} {fork : Fork}
    {a b : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (ok : processBlsToExecutionChanges config checks a body = .ok b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) := by
  unfold processBlsToExecutionChanges at ok
  split at ok
  · rename_i capella
    have folded : (body.blsToExecutionChanges capella).data.toList.foldlM
        (processBlsToExecutionChange config checks) a = .ok b := by
      simpa only [Array.foldlM_toList] using ok
    exact runFacts_of_frame
        (BlockFrame.foldlM (fun _ _ _ one => frame_processBlsToExecutionChange one) folded)
      (RegistryLifecycle.foldlM (fun _ _ _ one => registryLifecycle_processBlsToExecutionChange one)
            folded)
  · cases ok
    exact runFacts_of_frame (.refl a) (.refl a)

theorem runFacts_consolidationRequest {x : ForkedBeaconState preset} {fork : Fork}
    {electra : .pectra ≤ fork} {a b : BeaconState preset fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config a electra request = .ok b) :
    getCurrentEpoch b = getCurrentEpoch a ∧
    (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
      BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b) :=
  runFacts_of_frame (frame_processConsolidationRequest ok)
    (registryLifecycle_processConsolidationRequest ok)

end

/-- The tags of an initial queue are distinct initial positions. -/
private theorem initialTags_tags (queue : List PendingConsolidation) :
    (initialTags queue).map (·.tag) = (List.range' 0 queue.length).map QueueTag.initial := by
  have spread := List.zipIdx_map_snd 0 queue
  simp only [initialTags, List.map_map]
  rw [← spread, List.map_map]
  rfl

/-- A reserved history from `x`, paying only between distinct keys, gives the selected inputs. -/
private theorem selectedInputs_of_history {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) {high : Nat}
    (supported : Supported shared tail high) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) (electra : .pectra ≤ x.fork)
    {rounding : Nat → Nat} {before after : Ownership} {queue : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)} {allocations : List OwnedRelease}
    {calls : List (IndexedDepartureCall preset config)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0 events
      (initialTags (x.state.pendingConsolidations electra).data.toList) queue
      payments allocations calls before after)
    (paying : ∀ pair ∈ payments, Paying pair.2) :
    ∃ calls : List (IndexedDepartureCall preset config),
    ∃ final consumed paidTags : List TaggedEntry,
    ∃ selected : List SelectedCharge, ∃ payments : List (Payment preset),
      FreshPaymentCoverage (config := config) events
        (initialTags (x.state.pendingConsolidations electra).data.toList)
        final consumed paidTags payments calls ∧
      FreshTags (config := config) (consumed ++ final) calls ∧
      paidTags.Sublist consumed ∧ SelectedPayments selected payments paidTags ∧
      ActualPaymentCoverage events payments
        (x.state.pendingConsolidations electra).data.toList := by
  obtain ⟨genesis, _, _, _, early, endEpoch, guard⟩ := id supported
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, _, delayTwo, _⟩ := id guard
    omega
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨consumed, appended, replay, paidSub, pairs, perm, sizes, facts⟩ :=
    history.counters_original.2.2.2.2.2.2.2
  let isFresh : TaggedEntry × Payment preset → Bool := fun pair =>
    pair.1.tag.isFresh
  let fresh := payments.filter isFresh
  have freshMember : ∀ pair ∈ fresh, pair ∈ payments ∧ ∃ n, pair.1.tag = .fresh n := by
    intro pair member
    obtain ⟨inside, chosen⟩ := List.mem_filter.mp member
    refine ⟨inside, ?_⟩
    cases kind : pair.1.tag with
    | fresh n => exact ⟨n, rfl⟩
    | initial p => simp [isFresh, kind] at chosen
  refine ⟨calls, queue, consumed, fresh.map Prod.fst,
    fresh.map (fun pair => ⟨pair.2.source, pair.1.amount, pair.1.epoch, pair.2.epoch⟩),
    fresh.map Prod.snd, ⟨payments, replay, rfl, rfl⟩, ⟨?_, ?_⟩,
    ((List.filter_sublist).map _).trans paidSub, ⟨by simp, by simp, fun i => ?_⟩, ?_⟩
  · -- Initial tags are distinct initial positions; appended tags are distinct fresh positions.
    have appendedTags : appended.map (·.tag) =
        (List.range' 0 appended.length).map QueueTag.fresh := by
      apply List.ext_getElem (by simp)
      intro k inside _
      simpa using (facts k (by simpa using inside)).1
    have nodup : ((initialTags (x.state.pendingConsolidations electra).data.toList ++
        appended).map (·.tag)).Nodup := by
      rw [List.map_append, initialTags_tags, appendedTags, List.nodup_append]
      refine ⟨(List.nodup_range').map fun _ _ same => QueueTag.initial.inj same,
        (List.nodup_range').map fun _ _ same => QueueTag.fresh.inj same, ?_⟩
      intro a left b right same
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp left
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp right
      cases same
    exact (perm.map _).nodup_iff.mpr nodup
  · -- A fresh tag is an appended tag, pointing at its call.
    intro tag member n kind
    rcases List.mem_append.mp (perm.subset member) with initial | added
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp initial
      cases kind
    · obtain ⟨k, inside, rfl⟩ := List.getElem_of_mem added
      obtain ⟨tagEq, called, found, index, amount, epoch⟩ := facts k inside
      rw [kind, Nat.zero_add] at tagEq
      cases tagEq
      exact ⟨called, found, index, amount, epoch⟩
  · -- Each selected charge reads its payment and its fresh tag.
    have inside : i.val < fresh.length := by simpa using i.isLt
    obtain ⟨member, n, kind⟩ := freshMember _ (List.getElem_mem inside)
    obtain ⟨source, target⟩ := pairs _ member
    refine ⟨(fresh[i.val]).2, (fresh[i.val]).1, by simp [inside], by simp [inside],
      paying _ member, ⟨n, kind⟩, source.symm, target.symm, ?_, ?_, ?_, ?_⟩ <;> simp
  · -- The fresh payments are the payments from sources outside the initial queue.
    have lifecycle : ∀ e ∈ events, RegistryLifecycle x.state e.before.state := fun e member =>
      (replay_event_provenance shared tail genesis early high endEpoch events replayed e
        member).1
    have notInitial := history.fresh_not_initial shared genesis electra xEarly delay lifecycle
    have covered := history.actual_payment_coverage electra notInitial
    rw [show (((payments.zip allocations).filter fun pair =>
        pair.1.1.tag.isFresh).map
          fun pair => pair.1.2) = fresh.map Prod.snd from
      zip_filter_fst_map isFresh Prod.snd payments allocations
        history.paired_rounds.length_eq] at covered
    exact covered

section

open Cryptography.Bls

/-- The facts at the epoch input of a slot step, read from the run and its cache step.

The cache step writes only roots and the latest header.

So every fact of the run's end state holds at the epoch input as well. -/
private theorem epochInput_facts {g x u : ForkedBeaconState preset}
    {s : BeaconState preset u.fork}
    (shared : Run config checks g x) (pre : Run config checks x u)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (early : u.fork < .glamsterdam)
    (cached : processSlot u.state = .ok s) :
    BalancesMatch s ∧ ExitsOrdered s ∧
      PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s ∧
      (∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
        v.exitEpoch ≠ FAR_FUTURE_EPOCH →
          v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            v.withdrawableEpoch.toNat) ∧
      (∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) ∧
      (∀ v ∈ s.validators.data,
        v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset u.fork v) ∧
      (∀ electra : .pectra ≤ u.fork, ∀ c ∈ (s.pendingConsolidations electra).data.toList,
        c.sourceIndex ≠ c.targetIndex) ∧
      RegistryLifecycle x.state s ∧ getCurrentEpoch x.state ≤ getCurrentEpoch s ∧
      getCurrentEpoch s < FAR_FUTURE_EPOCH := by
  have run := shared.append pre
  have invariant := (run_justified_separated run genesis).1
  have start := currentEpoch_le_of_chainSteps pre.chainSteps
  have bounded := getCurrentEpoch_succ_lt_farFuture twoSlots u.state
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cached
  exact ⟨invariant.balancesMatch, invariant.exitsOrdered,
    run.pendingConsolidationsOrdered genesis early delay,
    run.exit_withdrawable_delay genesis,
    run.activationExitOrder genesis,
    run.effectiveBalance_capped genesis caps.activation caps.compounding early,
    run.pendingConsolidations_apart genesis early delay,
    pre.registryLifecycle.trans (.of_data rfl), start,
    UInt64.lt_iff_toNat_lt.mpr (by
      change (getCurrentEpoch u.state).toNat < FAR_FUTURE_EPOCH.toNat
      omega)⟩

/-- Fresh tags keep their source exits along a registry lifecycle, for any sublist of tags. -/
private theorem FreshExits.lifecycle {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {queue suffix : List TaggedEntry}
    (held : FreshExits s queue) (life : RegistryLifecycle s t)
    (within : ∀ tag ∈ suffix, tag ∈ queue) : FreshExits t suffix := by
  intro tag member n tagged
  obtain ⟨v, found, epochEq, assigned⟩ := held tag (within tag member) n tagged
  obtain ⟨w, located, kept⟩ := life.validators _ v found
  have same := kept.exitEpoch assigned
  exact ⟨w, located, same ▸ epochEq, same ▸ assigned⟩

end

section

open Cryptography.Bls Uint64

/-- A slot step inside an epoch records no balance event and moves only the slot and roots.

So the replay over it is one frame, and the retired set and both covers carry over. -/
private theorem reservedReplay_slot_inside {x u v : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {queue : List TaggedEntry} {owned : Ownership}
    {eventPosition paymentPosition callPosition : Nat}
    (ok : advanceSlotAcross config checks u = .ok v)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (nonlast : ∀ next, addChecked u.state.slot 1 = .ok next →
      next % preset.SLOTS_PER_EPOCH ≠ 0)
    (reserve : ReserveCut x high u (getCurrentEpoch u.state) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue u))
    (retired : RetiredActivated u.state owned.retired)
    (cover : EndpointCoverAll x u owned) (future : FutureEffectiveCover x u owned) :
    events = [] ∧
      ReservedReplay (config := config) (checks := checks) x high rounding
        u (getCurrentEpoch u.state) v (getCurrentEpoch v.state)
        eventPosition paymentPosition callPosition [] queue queue [] [] [] owned owned ∧
      RetiredActivated v.state owned.retired ∧ EndpointCoverAll x v owned ∧
      FutureEffectiveCover x v owned ∧ ∀ i, effectiveAt v i = effectiveAt u i := by
  obtain ⟨fork, s⟩ := u
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
  have frame := reservedFrame_advanceSlot_inside (config := config) (checks := checks)
    (rounding := rounding) advanceOk nonlast reserve assignment erasure
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, advancedEq⟩ :=
    advanceSlot_ok advanceOk
  change next.toNat = s.slot.toNat + 1 at sum
  have checked : addChecked s.slot 1 = .ok next :=
    addChecked_ok_iff.mpr ⟨by
      change s.slot.toNat + 1 < 2 ^ 64
      have small := next.toNat_lt
      omega, sum⟩
  have notLast := nonlast next checked
  simp only [epochIfLast, notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
  subst epoched
  -- No upgrade is due off the first slot of an epoch.
  have notDue : upgradeDue config (⟨fork, advanced⟩ : ForkedBeaconState preset) = false := by
    simp [upgradeDue, advancedEq, notLast]
  have stays : v = ⟨fork, advanced⟩ := by
    rw [processUpgrades.eq_def] at upgrades
    simp only [notDue, Bool.false_eq_true, pure, Except.pure] at upgrades
    exact (Except.ok.inj upgrades).symm
  subst stays
  have noCrossing : upgradeBalanceReplay (config := config) (checks := checks)
      (⟨fork, advanced⟩ : ForkedBeaconState preset) = .ok [] := by
    rw [upgradeBalanceReplay.eq_def]
    simp only [notDue, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  have nextOk : liftAccessor (liftArith (Uint64.addChecked s.slot 1)) =
      (Except.ok next : Except TransitionError Slot) := by
    rw [checked]; rfl
  simp only [Step.balanceEvents, cachedOk, nextOk, notLast, ↓reduceIte, advanceOk, noCrossing,
    bind, Except.bind, pure, Except.pure, List.append_nil, Except.ok.injEq] at replayed
  have sameEpoch : getCurrentEpoch advanced = getCurrentEpoch s := by
    apply UInt64.toNat_inj.mp
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, advancedEq]
    exact nextSlot_epoch_of_inside sum notLast
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  subst advancedEq
  refine ⟨replayed.symm, .nil frame, retired.lifecycle (.of_data rfl), ?_,
    futureCover_records (u := s) rfl (UInt64.le_of_eq sameEpoch.symm) future, ?_⟩
  · simpa only [EndpointCoverAll, actualBalanceAt, sameEpoch] using cover
  · intro i
    rfl

/-- The last slot of an epoch, before any upgrade.

It runs the cache, the epoch through its pending consolidations and suffix, and the slot write. -/
private theorem reservedReplay_slot_last {g x : ForkedBeaconState preset} {fork : Fork}
    {s cached epoched middle : BeaconState preset fork} {nextSlot : Slot}
    {recorded : List (BalanceEvent preset)} {high : Nat} {rounding : Nat → Nat}
    {queue : List TaggedEntry} {owned : Ownership}
    {eventPosition paymentPosition callPosition : Nat}
    (shared : Run config checks g x) (pre : Run config checks x ⟨fork, s⟩)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch s).toNat ≤ high + 1)
    (cachedOk : processSlot s = .ok cached)
    (epochOk : processEpoch config checks cached = .ok epoched)
    (sum : nextSlot.toNat = s.slot.toNat + 1) (last : nextSlot % preset.SLOTS_PER_EPOCH = 0)
    (middleOk : epochBeforePayments config checks cached = .ok middle)
    (recordOk : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, recorded))
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (retired : RetiredActivated s owned.retired)
    (cover : EndpointCoverAll x ⟨fork, s⟩ owned)
    (future : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (fresh : FreshExits s queue)
    (provenance : ∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
      (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH))
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      owned.original tag.entry.sourceIndex.toNat = 0) :
    ∃ (queue' : List TaggedEntry) (payments : List (TaggedEntry × Payment preset))
      (allocations : List OwnedRelease) (owned' : Ownership),
      ReservedReplay (config := config) (checks := checks) x high rounding
        ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, { epoched with slot := nextSlot }⟩
        (getCurrentEpoch { epoched with slot := nextSlot })
        eventPosition paymentPosition callPosition recorded queue queue' payments allocations []
        owned owned' ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, { epoched with slot := nextSlot }⟩ ⟨fork, { epoched with slot := nextSlot }⟩
        (getCurrentEpoch { epoched with slot := nextSlot })
        (getCurrentEpoch { epoched with slot := nextSlot }) queue' owned' owned' ∧
      OwnershipBefore (eventPosition + recorded.length) (paymentPosition + payments.length)
        owned' ∧
      RetiredActivated { epoched with slot := nextSlot } owned'.retired ∧
      EndpointCoverAll x ⟨fork, { epoched with slot := nextSlot }⟩ owned' ∧
      FutureEffectiveCover x ⟨fork, { epoched with slot := nextSlot }⟩ owned' ∧
      (∀ tag ∈ queue', tag ∈ queue) ∧
      (∀ e ∈ recorded, e.source = .consolidations →
        PendingConsolidationInvariant config e.before.state) ∧
      (∀ pair ∈ payments,
        pair.2.epoch ≤ (getCurrentEpoch { epoched with slot := nextSlot }).toNat) ∧
      (∀ pair ∈ payments, ∀ n, pair.1.tag = .fresh n → ∃ w,
        pair.2.before.state.validators.data[pair.2.source]? = some w ∧
          pair.1.epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            w.withdrawableEpoch.toNat) ∧
      (∀ pair ∈ payments, Paying pair.2) ∧
      (0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat → ∀ down : Nat → Prop,
        (∀ i, owned.original i ≤ effectiveAt ⟨fork, s⟩ i +
          (if down i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) →
        ∀ i, owned'.original i ≤ effectiveAt ⟨fork, { epoched with slot := nextSlot }⟩ i +
          (if down i ∨ effectiveAt ⟨fork, { epoched with slot := nextSlot }⟩ i <
              effectiveAt ⟨fork, s⟩ i then
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by omega
  have earlyX : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) early
  obtain ⟨matched, exits, ordered, delayed, activationOrder, capped, apartAll, startLife,
    startCurrent, finite⟩ :=
    epochInput_facts (u := ⟨fork, s⟩) shared pre genesis caps delay twoSlots early cachedOk
  -- The cache keeps the registry, the balances, the slot and the queue.
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have sameEpoch : getCurrentEpoch cached = getCurrentEpoch s := by
    simp only [getCurrentEpoch, processSlot_slot cachedOk]
  have cacheFrame : ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, cached⟩ (getCurrentEpoch s) (getCurrentEpoch cached) queue owned owned := by
    rw [sameEpoch]
    exact reservedFrame_cache cachedOk reserve assignment erasure
  obtain ⟨_, _, _, _, _, _, cachedErasure, _, cachedReserve⟩ := id cacheFrame
  -- The stages before the payments, as the replay records them.
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, rewardEvents,
    limit, prefixTrace, justifiedOk, scoredOk, rewardsOk, registry, slashings, limitOk, resetOk,
    depositsOk, consolidationsOk, replay, recordedEq⟩ :=
    funding_epoch_site_limit middleOk recordOk
  -- The epoch's own trace runs the same prefix, so its suffix starts at `middle`.
  have suffixTrace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) middle epoched := by
    have trace := processEpoch_trace epochOk
    change EpochTrace _ (EpochStage.prefixStages ++
      (EpochStage.middleStages ++ EpochStage.tailStages)) cached epoched at trace
    obtain ⟨other, headTrace, tailTrace⟩ := EpochTrace.append_iff.mp trace
    have same : other = middle := by
      have run := EpochTrace.run_ok_iff.mpr headTrace
      rw [← epochBeforePayments_eq_run] at run
      exact Except.ok.inj (run.symm.trans middleOk)
    exact same ▸ tailTrace
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have finiteNat := UInt64.lt_iff_toNat_lt.mp finite
  obtain ⟨next, nextOk⟩ : ∃ next, addChecked (getCurrentEpoch cached) 1 = .ok next := by
    refine ⟨getCurrentEpoch cached + 1, addChecked_ok_iff.mpr ⟨?_, ?_⟩⟩
    · simp only [UInt64.toNat_one]
      omega
    · rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  have nextNat : next.toNat = (getCurrentEpoch cached).toNat + 1 := by
    simpa only [UInt64.toNat_one] using (addChecked_ok_iff.mp nextOk).2
  -- The cache keeps the registry, the balances and the slot.
  have cachedValidators : cached.validators = s.validators := by rw [cachedEq]
  have cachedBalances : cached.balances = s.balances := by rw [cachedEq]
  have cachedSlot : cached.slot = s.slot := processSlot_slot cachedOk
  have cachedRetired : RetiredActivated cached owned.retired :=
    retired.lifecycle (.of_data (congrArg (·.data) cachedValidators))
  have cachedCover : EndpointCoverAll x ⟨fork, cached⟩ owned :=
    endpointCoverAll_records cachedValidators cachedBalances cachedSlot cover
  have cachedFuture : FutureEffectiveCover x ⟨fork, cached⟩ owned :=
    futureCover_records cachedValidators (UInt64.le_of_eq sameEpoch.symm) future
  -- The queue is the actual pending queue, so it inherits the run's queue facts.
  have queueEq : queue.map (·.entry) = (cached.pendingConsolidations electra).data.toList := by
    rw [cachedErasure]
    simp only [pendingQueue, electra, ↓reduceDIte]
  have entryOf : ∀ tag ∈ queue, tag.entry ∈ (cached.pendingConsolidations electra).data.toList :=
    fun tag member => queueEq ▸ List.mem_map_of_mem member
  have unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup := by
    have nodup := (ordered.1 electra).1
    rw [← queueEq, List.map_map] at nodup
    exact nodup
  have apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex :=
    fun tag member => apartAll electra _ (entryOf tag member)
  have sources : ∀ tag ∈ queue, ∃ w,
      cached.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
        w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro tag member
    obtain ⟨w, found, activated, _⟩ := (ordered.1 electra).2 _ (entryOf tag member)
    refine ⟨w, found, fun far' => ?_⟩
    rw [far'] at activated
    exact absurd (UInt64.lt_of_le_of_lt activated finite) (UInt64.lt_irrefl _)
  have slashedSpan := epochPrefix_slashedSpan pre caps.activation caps.compounding early
    cachedOk justifiedOk scoredOk rewardsOk registry slashings resetOk depositsOk
  have horizon : next.toNat ≤ horizonEnd x high := by
    have epochs : (getCurrentEpoch cached).toNat = (getCurrentEpoch s).toNat := by
      rw [sameEpoch]
    unfold horizonEnd driftHorizon
    omega
  obtain ⟨_, suffix, _, payments, allocations, final, pass, _, _, replayed, frameEnd, ownedEnd,
    retiredEnd, coverEnd, futureEnd, effectiveBound⟩ :=
    reservedReplay_epochNext_lowered (x := x) (high := high) (rounding := rounding)
      (eventPosition := eventPosition) (paymentPosition := paymentPosition)
      (callPosition := callPosition) electra early matched justifiedOk scoredOk rewardsOk replay
      registry slashings limitOk resetOk depositsOk consolidationsOk suffixTrace cachedReserve
      assignment cachedErasure prior cachedRetired cachedCover cachedFuture startLife
      (UInt64.lt_of_le_of_lt startCurrent finite) startCurrent ordered exits finite delayed
      delayTwo activationOrder nextOk twoSlots capped unique apart sources initialZero
      slashedSpan horizon (Run.pendingConsolidationsOrdered shared genesis earlyX delay)
      (run_slashed_exit_assigned shared genesis caps.activation caps.compounding earlyX delay)
      provenance
  -- The pass keeps a sublist of the queue, and pays from states with the pass input's registry.
  have shape := pass.pass_shape
  -- The prefix facts at the pass input: its registry lifecycle and the withdrawal delay.
  have deposits : processPendingDeposits config checks reset electra = .ok deposited := by
    simpa only [EpochStage.Edge, electra, ↓reduceDIte] using depositsOk
  obtain ⟨_, _, _, _, _, _, _, _, _, _, depositedLife, _, depositedDelay, _⟩ :=
    reservedReplay_epochPrefixDeposits_facts (x := x) (high := high) (rounding := rounding)
      (eventPosition := eventPosition) (paymentPosition := paymentPosition)
      (callPosition := callPosition) electra early matched justifiedOk scoredOk rewardsOk replay
      registry slashings limitOk resetOk deposits cachedReserve assignment cachedErasure prior
      cachedRetired startLife (UInt64.lt_of_le_of_lt startCurrent finite) ordered exits finite
      delayed delayTwo
  have freshDeposited : FreshExits deposited queue :=
    fresh.lifecycle ((RegistryLifecycle.of_data (congrArg (·.data) cachedValidators)).trans
      depositedLife) (fun _ member => member)
  have freshDelay : ∀ pair ∈ payments, ∀ n, pair.1.tag = .fresh n → ∃ w,
      pair.2.before.state.validators.data[pair.2.source]? = some w ∧
        pair.1.epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          w.withdrawableEpoch.toNat := by
    intro pair member n tagged
    obtain ⟨inQueue, sourceEq, _, _, w, beforeEq, sameRegistry⟩ := shape.2.2.2.2.1 pair member
    obtain ⟨v, found, epochEq, assigned⟩ := freshDeposited pair.1 inQueue n tagged
    refine ⟨v, ?_, ?_⟩
    · rw [beforeEq, sourceEq]
      change w.validators.data[_]? = some v
      rw [sameRegistry]; exact found
    · have := depositedDelay _ v found assigned
      omega
  -- Only the last recorded event moves pending consolidations, from the pass input.
  have orderedDeposited : PendingConsolidationsOrdered config
      (getCurrentEpoch deposited).toNat deposited :=
    depositsOk.pendingConsolidationsOrdered
      (epochTrace_pendingConsolidationsOrdered prefixTrace ordered)
  have recordStep : ∀ (source : BalanceSource)
      (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
      (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
      {pre post : BalanceReplay preset fork},
      recordBalance source limits action pre = .ok post → source ≠ .consolidations →
      (∀ e ∈ pre.2, e.source ≠ .consolidations) →
      ∀ e ∈ post.2, e.source ≠ .consolidations := by
    intro source limits action pre post ok notTransfer prior
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, _, _, _, rfl⟩ := ok
    intro e member
    rcases List.mem_append.mp member with old | added
    · exact prior e old
    · simp only [List.mem_singleton] at added
      subst added
      exact notTransfer
  have rewardSources : ∀ e ∈ rewardEvents, e.source ≠ .consolidations :=
    replayRewards_induction (config := config)
      (fun pre : BalanceReplay preset fork => ∀ e ∈ pre.2, e.source ≠ .consolidations)
      (fun prior ok => recordStep _ _ _ ok (by simp) prior)
      (fun which prior ok => recordStep _ _ _ ok
        (by rcases which with rfl | rfl <;> simp) prior)
      (by simp) replay
  have consolidationEvents : ∀ e ∈ recorded, e.source = .consolidations →
      PendingConsolidationInvariant config e.before.state := by
    intro e member transfer
    rw [recordedEq] at member
    simp only [electra, ↓reduceDIte, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (old | rfl) | rfl | rfl
    · exact absurd transfer (rewardSources e old)
    · cases transfer
    · cases transfer
    · exact orderedDeposited.1
  -- The stages before the payments record exactly the replay's events.
  rw [← recordedEq] at replayed
  have recordedLength : recorded.length = rewardEvents.length + 3 := by
    simp [recordedEq, electra]
  -- The epoch keeps the slot, so the slot write lands on the first slot of the next epoch.
  obtain ⟨justifiedState, justifiedStep, epochFrame⟩ := processEpoch_frame epochOk
  have epochedSlot : epoched.slot = s.slot :=
    epochFrame.slot.trans ((processJustificationAndFinalization_slot justifiedStep).trans
      cachedSlot)
  have checked : addChecked epoched.slot 1 = .ok nextSlot := by
    rw [epochedSlot]
    have small := nextSlot.toNat_lt
    refine addChecked_ok_iff.mpr ⟨?_, ?_⟩ <;> simp only [UInt64.toNat_one] <;> omega
  have advancedEpoch : getCurrentEpoch { epoched with slot := nextSlot } = next := by
    apply UInt64.toNat_inj.mp
    rw [nextNat, sameEpoch, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact nextSlot_epoch_of_boundary sum last
  have epochedEpoch : getCurrentEpoch epoched = getCurrentEpoch s := by
    simp only [getCurrentEpoch, epochedSlot]
  have later : getCurrentEpoch epoched ≤ getCurrentEpoch { epoched with slot := nextSlot } := by
    rw [advancedEpoch, epochedEpoch, ← sameEpoch]
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨_, _, _, _, endAssignment, _, endErasure, _, endReserve⟩ := frameEnd
  have slotFrame := reservedFrame_slot (config := config) (checks := checks)
    (rounding := rounding) checked endReserve endAssignment endErasure
  obtain ⟨_, _, _, _, _, _, slotErasure, _, slotReserve⟩ := id slotFrame
  have whole := ReservedReplay.append (.nil cacheFrame)
    (by simpa only [List.length_nil, Nat.add_zero] using replayed)
  have full := ReservedReplay.append whole (.nil (by simpa only [] using slotFrame))
  rw [advancedEpoch]
  have sameEffective : ∀ i, effectiveAt ⟨fork, cached⟩ i = effectiveAt ⟨fork, s⟩ i := by
    intro i
    simp only [effectiveAt, cachedValidators]
  refine ⟨suffix, payments, allocations, lowerOriginal final ⟨fork, epoched⟩, ?_,
    reservedFrame_refl slotReserve endAssignment slotErasure,
    by simpa only [recordedLength] using ownedEnd,
    retiredEnd.lifecycle (.of_data rfl), ?_, ?_, fun tag member => shape.1.1.subset member,
    consolidationEvents, fun pair member => ?_, freshDelay, shape.2.2.2.2.2 apart,
    fun increment down before i => ?_⟩
  · simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero] using full
  · refine endpointCover_mono (u := ⟨fork, epoched⟩) ?_ (fun _ => Nat.le_refl _) coverEnd
    intro i w found clean notExited current
    exact ⟨w, found, clean, notExited, UInt64.le_trans later current, rfl, le_refl _⟩
  · exact futureCover_records (u := epoched) (v := { epoched with slot := nextSlot }) rfl later
      futureEnd
  · exact Nat.le_of_eq (shape.2.2.2.2.1 pair member).2.2.1
  · have bound := effectiveBound increment down
      (fun i => by rw [sameEffective i]; exact before i) i
    rw [sameEffective i] at bound
    exact bound

/-- The reserved replay of one slot step of a shared run.

Inside an epoch the step is one frame.

At the last slot of an epoch it runs the cache, the epoch and the slot write.

The fork upgrades follow, and they record nothing from Electra. -/
private theorem reservedReplay_slotStep :
    SlotStepReplay (preset := preset) (config := config) (checks := checks) := by
  intro g x u v high rounding queue owned eventPosition paymentPosition callPosition shared pre
    genesis caps twoSlots delayTwo _ electra early endEpoch ok events replayed reserve assignment
    erasure prior retired cover future fresh provenance initialZero
  obtain ⟨fork, s⟩ := u
  have life : RegistryLifecycle s v.state := RegistryLifecycle.chainStep (Step.slot ok).chainStep
  have startEarly : fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  -- The slot step keeps the consolidation queue, across its epoch and its upgrades.
  have trace : ∀ target : .pectra ≤ v.fork,
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) []
        (v.state.earliestConsolidationEpoch target)
        (v.state.consolidationBalanceToConsume target) := by
    intro target
    obtain ⟨epochEq, balanceEq⟩ := advanceSlotAcross_consolidationQueue (config := config)
      (checks := checks) (u := ⟨fork, s⟩) electra target early ok
    rw [epochEq, balanceEq]
    exact .nil _ _
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, advancedEq⟩ :=
    advanceSlot_ok advanceOk
  change nextSlot.toNat = s.slot.toNat + 1 at sum
  have checked : addChecked s.slot 1 = .ok nextSlot := by
    have small := nextSlot.toNat_lt
    refine addChecked_ok_iff.mpr ⟨?_, ?_⟩ <;> simp only [UInt64.toNat_one] <;> omega
  by_cases last : nextSlot % preset.SLOTS_PER_EPOCH = 0
  · simp only [epochIfLast, last, ↓reduceIte] at epochedOk
    obtain ⟨middle, headTrace, _⟩ := processEpoch_suffix_framePath epochedOk
    have middleOk : epochBeforePayments config checks cached = .ok middle :=
      (epochBeforePayments_eq_run config checks cached).trans
        (EpochTrace.run_ok_iff.mpr headTrace)
    obtain ⟨recorded, recordOk⟩ := epochBalanceReplay_before middleOk
    obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
    have nextOk : liftAccessor (liftArith (Uint64.addChecked s.slot 1)) =
        (Except.ok nextSlot : Except TransitionError Slot) := by
      rw [checked]; rfl
    have eventsEq := Except.ok.inj (replayed.symm.trans
      (Step.balanceEvents_epoch_slot ok cachedOk nextOk last recordOk advanceOk crossingOk))
    subst advancedEq
    obtain rfl := upgradeBalanceReplay_electra_nil (config := config) (checks := checks)
      (u := ⟨fork, { epoched with slot := nextSlot }⟩) electra crossingOk
    rw [List.append_nil] at eventsEq
    subst eventsEq
    obtain ⟨queue', payments, allocations, owned', epochReplay, epochFrame, _,
      epochRetired, epochCover, epochFuture, within, consolidationEvents, paymentEpochs,
      freshDelay, paying, lastBound⟩ :=
      reservedReplay_slot_last (eventPosition := eventPosition)
        (paymentPosition := paymentPosition) (callPosition := callPosition) shared pre genesis
        caps twoSlots delayTwo electra startEarly endEpoch cachedOk epochedOk sum last middleOk
        recordOk reserve assignment erasure prior retired cover future fresh provenance
        initialZero
    obtain ⟨_, _, upgraded, upgradeReplay, _, upgradeRetired, upgradeCover, upgradeFuture⟩ :=
      reservedReplay_upgrades (eventPosition := eventPosition + events.length)
        (paymentPosition := paymentPosition + payments.length) (callPosition := callPosition)
        upgrades electra early crossingOk epochFrame epochRetired epochCover
        epochFuture
    cases upgradeReplay with
    | nil upgradeFrame =>
      obtain ⟨_, later, upgradeOwned, _, assignmentV, _, erasureV, _, reserveV⟩ := id upgradeFrame
      have full : ReservedReplay (config := config) (checks := checks) x high rounding
          ⟨fork, s⟩ (getCurrentEpoch s) v (getCurrentEpoch v.state)
          eventPosition paymentPosition callPosition events queue queue' payments allocations []
          owned upgraded := by
        simpa only [List.append_nil, List.length_nil, Nat.add_zero] using
          epochReplay.append (.nil upgradeFrame)
      refine ⟨queue', payments, allocations, upgraded, full, reserveV, assignmentV, erasureV,
        full.counters prior, upgradeRetired, upgradeCover, upgradeFuture,
        fresh.lifecycle life within, consolidationEvents, fun pair member => ?_, freshDelay,
        paying, fun increment down before i => ?_, trace⟩
      · exact Nat.le_trans (paymentEpochs pair member) (UInt64.le_iff_toNat_le.mp later)
      · -- The upgrades keep the registry and only lower the originals.
        have upgradesData := processUpgrades_validators_of_electra (config := config)
          (checks := checks) (s := ⟨fork, { epoched with slot := nextSlot }⟩) (t := v) electra
          early upgrades
        have sameV : effectiveAt v i = effectiveAt ⟨fork, { epoched with slot := nextSlot }⟩ i := by
          simp only [effectiveAt, upgradesData]
        have lowered := upgradeOwned.2.2.2.2.2.2 i
        have bound := lastBound increment down before i
        -- A drop at the epoch is a drop between the first two states of the step's path.
        have path : (Step.slot ok).balancePath =
            [⟨fork, s⟩, ⟨fork, { epoched with slot := nextSlot }⟩, v] := by
          simp [Step.balancePath, advanceOk, Except.toOption]
        rw [sameV]
        by_cases d : down i ∨ effectiveAt ⟨fork, { epoched with slot := nextSlot }⟩ i <
            effectiveAt ⟨fork, s⟩ i
        · have drop : down i ∨ StepDrop (Step.slot ok) i := by
            rcases d with d | d
            · exact .inl d
            · exact .inr ⟨0, _, _, by simp [path], by simp [path], d⟩
          rw [ite_eq_left d] at bound
          rw [ite_eq_left drop]
          omega
        · rw [ite_eq_right d] at bound
          split <;> omega
  · have nonlast : ∀ next, addChecked s.slot 1 = .ok next →
        next % preset.SLOTS_PER_EPOCH ≠ 0 := by
      intro next computed
      rw [checked] at computed
      cases computed
      exact last
    obtain ⟨rfl, insideReplay, insideRetired, insideCover, insideFuture, insideEffective⟩ :=
      reservedReplay_slot_inside (eventPosition := eventPosition)
        (paymentPosition := paymentPosition) (callPosition := callPosition)
        ok replayed nonlast reserve assignment erasure retired cover future
    cases insideReplay with
    | nil insideFrame =>
      obtain ⟨_, _, _, _, assignmentV, _, erasureV, _, reserveV⟩ := id insideFrame
      refine ⟨queue, [], [], owned, .nil insideFrame, reserveV, assignmentV, erasureV,
        by simpa only [List.length_nil, Nat.add_zero] using prior, insideRetired, insideCover,
        insideFuture, fresh.lifecycle life (fun _ member => member), by simp, by simp, by simp,
        by simp, fun _ down before i => ?_, trace⟩
      have bound := before i
      rw [insideEffective i]
      by_cases d : down i
      · rw [ite_eq_left (Or.inl d)]
        rw [ite_eq_left d] at bound
        exact bound
      · rw [ite_eq_right d] at bound
        split <;> omega

/-- A switch to compounding credentials keeps the reserve cut, with the same ownership.

Every validator keeps its fields other than its credentials.

So support, relevance and the effective balance read the same.

Balances and capped balances do not rise. -/
private theorem reserveCut_switch {x : ForkedBeaconState preset} {high : Nat} {fork : Fork}
    {u v : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {suffix : List PendingConsolidation} {o : Ownership}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator u electra index = .ok v)
    (reserve : ReserveCut x high ⟨fork, u⟩ (getCurrentEpoch u) suffix o) :
    ReserveCut x high ⟨fork, v⟩ (getCurrentEpoch v) suffix o := by
  obtain ⟨epoch, effective, lookup⟩ := switchToCompoundingValidator_lookup compounding ok
  obtain ⟨valid, retiredCut, original, newReference, endpoint, pending, queued, fresh, initial,
    supported⟩ := reserve
  -- A relevant index after was relevant before.
  have relevant : ∀ i, FundingRelevant (⟨fork, v⟩ : ForkedBeaconState preset)
      (getCurrentEpoch u) suffix i → FundingRelevant ⟨fork, u⟩ (getCurrentEpoch u) suffix i := by
    intro i ⟨w, found, reason⟩
    obtain ⟨w₀, _, found₀, rfl, _⟩ := lookup i w found
    exact ⟨w₀, found₀, reason⟩
  rw [epoch]
  refine ⟨valid, ?_, original, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member w found
    obtain ⟨w₀, _, found₀, rfl, _⟩ := lookup i w found
    exact retiredCut i member w₀ found₀
  · intro i reference notRetired relevantV
    have bound := newReference i reference notRetired (relevant i relevantV)
    obtain ⟨w, found, _⟩ := relevantV
    obtain ⟨w₀, _, found₀, rfl, _, capped⟩ := lookup i w found
    simp only [potential, found, found₀, Option.map_some, Option.getD_some] at bound ⊢
    exact (max_le_max (Nat.le_refl _) capped).trans bound
  · intro i initialV w xFound active clean notFar found supportedV
    obtain ⟨w₀, _, found₀, rfl, _, capped⟩ := lookup i w found
    rw [effective i]
    exact (max_le_max (Nat.le_refl _) capped).trans
      (endpoint i initialV w₀ xFound active clean notFar found₀ supportedV)
  · intro i initialPending notRetired relevantV w found
    obtain ⟨w₀, _, found₀, rfl, _, capped⟩ := lookup i w found
    exact capped.trans (pending i initialPending notRetired (relevant i relevantV) w₀ found₀)
  · intro c member w found due notReference
    obtain ⟨w₀, _, found₀, rfl, _, capped⟩ := lookup _ w found
    exact capped.trans (queued c member w₀ found₀ due notReference)
  · intro i w found notReference notQueued quiet reason
    obtain ⟨w₀, _, found₀, rfl, _, capped⟩ := lookup i w found
    rw [effective i]
    exact (max_le_max (Nat.le_refl _) capped).trans
      (fresh i w₀ found₀ notReference notQueued quiet reason)
  · intro i initialPending w initialV found xFound active notRetired relevantV
    obtain ⟨w₀, _, found₀, rfl, _, capped⟩ := lookup i w found
    obtain ⟨heldCapped, heldEffective⟩ := initial i initialPending w₀ initialV found₀ xFound active
      notRetired (relevant i relevantV)
    exact ⟨capped.trans heldCapped, (effective i).trans_le heldEffective⟩
  · intro i w found supportedV notPrevious
    obtain ⟨w₀, _, found₀, rfl, _⟩ := lookup i w found
    rw [effective i]
    exact supported i w₀ found₀ supportedV notPrevious

/-- Take a switch to compounding credentials, recorded as one non-transfer event.

It keeps the reserved replay with the same queue and ownership.

The frame, the retired set and both covers carry to the state after the switch. -/
theorem reservedReplay_switchToCompounding {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} (electra : .pectra ≤ fork)
    (ok : switchToCompoundingValidator s electra index = .ok t)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, s⟩ (getCurrentEpoch s) (getCurrentEpoch s) queue owned owned)
    (retired : RetiredActivated s owned.retired)
    (cover : EndpointCoverAll x ⟨fork, s⟩ owned)
    (future : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (e : BalanceEvent preset) (before : e.before = ⟨fork, s⟩) (after : e.after = ⟨fork, t⟩)
    (notTransfer : e.source ≠ .consolidations) :
    ReservedReplay (config := config) (checks := checks) x high rounding
        ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, t⟩ (getCurrentEpoch t)
        eventPosition paymentPosition callPosition [e] queue queue [] [] [] owned owned ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue owned owned ∧
      RetiredActivated t owned.retired ∧
      EndpointCoverAll x ⟨fork, t⟩ owned ∧ FutureEffectiveCover x ⟨fork, t⟩ owned := by
  obtain ⟨epoch, effective, lookup⟩ := switchToCompoundingValidator_lookup compounding ok
  obtain ⟨_, _, owning, assignment, _, erasure, _, reserve, _⟩ := id frame
  have reserveT := reserveCut_switch compounding ok reserve
  -- The pending consolidations, and so the tagged queue, are unchanged.
  have sameQueue :
      pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) = pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, electra, ↓reduceDIte,
      (switchToCompoundingValidator_consolidationQueues ok).1]
  have erasureT : QueueErasure queue (pendingQueue ⟨fork, t⟩) := by
    rw [sameQueue]
    exact erasure
  have frameT := reservedFrame_refl (config := config) (checks := checks) reserveT assignment
    erasureT
  have futureT : FutureEffectiveCover x ⟨fork, t⟩ owned := by
    apply futureCover_mono (u := ⟨fork, s⟩) ?_ (fun _ => Nat.le_refl _) future
    intro i w found later clean notExited
    obtain ⟨w₀, _, found₀, rfl, _⟩ := lookup i w found
    refine ⟨w₀, found₀, ?_, clean, notExited, rfl, (effective i).le⟩
    rw [← epoch]
    exact later
  refine ⟨?_, frameT, retired.lifecycle (registryLifecycle_switchToCompoundingValidator ok),
    endpointCover_switch compounding ok cover, futureT⟩
  obtain ⟨source, eventBefore, eventAfter, credit, debit⟩ := e
  dsimp only at before after notTransfer
  subst before after
  refine ReservedReplay.singleton_nonconsolidation
    (e := ⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩) notTransfer frame ?_ ?_
  · unfold TagEvent
    exact ⟨erasure, erasureT, .inl ⟨notTransfer, rfl, rfl, rfl, rfl⟩⟩
  · unfold ReservedEvent OwnedEvent
    refine ⟨?_, assignment, assignment, ?_⟩
    · split
      · exact absurd ‹_› notTransfer
      · exact ⟨rfl, rfl, .inr owning⟩
    · split
      · exact absurd ‹_› notTransfer
      · exact ⟨reserve, reserveT⟩

/-- The reserved replay of a tail from Electra, built step by step.

The replay starts at `x` with the initial ownership and its initial reserved frame.

A slot step extends it by the replay of a slot step, and a block step by the replay of a block.

Each step reads the queue provenance and the zero originals of initial tags from the replay so far.

It reads the run facts at its input from `shared` and the prefix.

This is the one run-level replay walk, and it follows the recursion of the run's balance events.

The funding bound of a run cannot carry the step.

Its motive is a fixed number.

Its step bound sees neither the replay so far nor the prefix events.

The floor induction recurses on epochs and sees no events. -/
private theorem reservedReplay_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electraX : .pectra ≤ x.fork) (rounding : Nat → Nat)
    (roundingAt : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (rest : Run config checks n y),
      (pre.snoc step).append rest = tail →
      ∀ (i : Nat) (v w : Validator), m.state.validators.data[i]? = some v →
        n.state.validators.data[i]? = some w →
        v.exitEpoch = FAR_FUTURE_EPOCH → w.exitEpoch ≠ FAR_FUTURE_EPOCH →
        NewReference x i → FirstDown pre i →
        rounding i = preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (slotStep : SlotStepReplay (preset := preset) (config := config) (checks := checks))
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ (before after : Ownership) (queue : List TaggedEntry)
      (payments : List (TaggedEntry × Payment preset)) (allocations : List OwnedRelease)
      (calls : List (IndexedDepartureCall preset config)),
      OwnedInitial x high before ∧
      ReservedReplay (config := config) (checks := checks) x high rounding
        x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0 events
        (initialTags (x.state.pendingConsolidations electraX).data.toList) queue
        payments allocations calls before after ∧
      ReserveCut x high y (getCurrentEpoch y.state) (queue.map (·.entry)) after ∧
      AssignmentCut rounding queue after ∧ QueueErasure queue (pendingQueue y) ∧
      OwnershipBefore events.length payments.length after ∧
      RetiredActivated y.state after.retired ∧
      EndpointCoverAll x y after ∧ FutureEffectiveCover x y after ∧
      FreshExits y.state queue ∧
      (∀ pair ∈ payments, pair.2.epoch ≤ (getCurrentEpoch y.state).toNat) ∧
      (∀ pair ∈ payments, ∀ n, pair.1.tag = .fresh n → ∃ v,
        pair.2.before.state.validators.data[pair.2.source]? = some v ∧
        pair.1.epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat) ∧
      (∀ pair ∈ payments, Paying pair.2) ∧
      (∀ electraY : .pectra ≤ y.fork, DepartureQueueTrace
        (x.state.earliestConsolidationEpoch electraX)
        (x.state.consolidationBalanceToConsume electraX)
        (calls.map (·.call)) (y.state.earliestConsolidationEpoch electraY)
        (y.state.consolidationBalanceToConsume electraY)) ∧
      ConsolidationCallSites preset config calls tail.consolidationSites ∧
      OriginalDown tail after := by
  unfold SlotStepReplay at slotStep
  obtain ⟨genesis, _, caps, _, early, endEpoch, guard⟩ := supported
  have delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, _, delay, _⟩ := id guard
    exact delay
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by omega
  have increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    obtain ⟨increment, _⟩ := id guard
    exact increment
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨initialOwned, initial, frame, cover, future⟩ :=
    reservedFrame_initial shared genesis xEarly high electraX rounding
  -- The sources of the queue at `x` have their exits assigned there.
  have initialSources := (shared.pendingConsolidation_invariant genesis xEarly electraX delay).2
  revert early endEpoch roundingAt
  induction tail generalizing events with
  | nil =>
    intro _ _ _
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    obtain ⟨_, _, _, assignment, _, erasure, _, reserve, _⟩ := id frame
    refine ⟨initialOwned, initialOwned, _, [], [], [], initial, .nil frame, reserve, assignment,
      erasure, initial.counters, initial.retiredActivated, cover, future, ?_, by simp, by simp,
      by simp, fun _ => .nil _ _, by simp [ConsolidationCallSites], originalDown_initial initial⟩
    -- No initial tag is fresh.
    intro tag member n fresh
    simp only [initialTags, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    cases fresh
  | @snoc middle last pre step ih =>
    intro roundingAt early endEpoch
    have middleEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have stepEpoch := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have within := stepEpoch.trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [within, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    obtain ⟨before, owned, queue, payments, allocations, calls, initialB, history, reserve,
      assignment, erasure, counted, retired, coverM, futureM, fresh, paidBy, delayed, paying,
      trace, sites, down⟩ := ih priorOk
        (fun p s' r split => roundingAt p s' (r.snoc step) (congrArg (Run.snoc · step) split))
        middleEarly within
    have middleElectra : .pectra ≤ middle.fork :=
      Nat.le_trans electraX (fork_le_of_chainSteps pre.chainSteps)
    have whole := shared.append pre
    -- The replay so far keeps its queue provenanced.
    have provenance := run_queue_provenance shared pre genesis middleEarly within priorOk electraX
      history initialB.counters
    obtain ⟨_, _, lowered, initialFrom, _⟩ := history.counters_original
    -- An initial tag names a source whose exit is assigned at `x`, so its original is zero.
    have initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
        owned.original tag.entry.sourceIndex.toNat = 0 := by
      intro tag member n tagged
      have entryIn := List.mem_map_of_mem (f := (·.entry)) (initialFrom tag member n tagged)
      rw [initialTags_entries] at entryIn
      obtain ⟨v, found, _, _, assigned⟩ := initialSources tag.entry entryIn
      have zero : before.original tag.entry.sourceIndex.toNat = 0 := by
        rw [initialB.2.2.2.2.2]
        simp [found, assigned]
      have := lowered tag.entry.sourceIndex.toNat
      omega
    -- Payments made so far are due by the end of the prefix.
    have paidLast : ∀ pair ∈ payments, pair.2.epoch ≤ (getCurrentEpoch last.state).toNat :=
      fun pair member => (paidBy pair member).trans stepEpoch
    -- The run facts at the step input.
    have invariant := (run_justified_separated whole genesis).1
    have slashedExit : SlashedExitAssigned middle.state := fun i v found flag =>
      run_slashed_exit_assigned whole genesis caps.activation caps.compounding middleEarly delay
        i v found flag
    have finite : getCurrentEpoch middle.state < FAR_FUTURE_EPOCH := by
      have ne := getCurrentEpoch_ne_farFuture twoSlots middle.state
      have bound := (getCurrentEpoch middle.state).toNat_lt
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      have apart : (getCurrentEpoch middle.state).toNat ≠ FAR_FUTURE_EPOCH.toNat :=
        fun same => ne (UInt64.toNat_inj.mp same)
      rw [UInt64.lt_iff_toNat_lt]
      omega
    cases step with
    | slot ok =>
      obtain ⟨queue', stepPayments, stepAllocations, owned', replay, reserve', assignment',
        erasure', counted', retired', cover', future', fresh', _, paid', delayed', paying',
        bound, trace'⟩ :=
        @slotStep g x middle last high rounding queue owned prior.length payments.length
          calls.length shared pre genesis caps twoSlots delayTwo electraX middleElectra early
          within ok added addedOk reserve assignment erasure counted retired coverM futureM fresh
          provenance initialZero
      refine ⟨before, owned', queue', payments ++ stepPayments, allocations ++ stepAllocations,
        calls ++ [], initialB, history.append (by simpa only [Nat.zero_add] using replay),
        reserve', assignment', erasure', by simpa only [List.length_append] using counted',
        retired', cover', future', fresh', ?_, ?_, ?_, fun electraY => ?_, ?_,
        originalDown_slot pre (Step.slot ok) down (bound increment)⟩
      · intro pair member
        rcases List.mem_append.mp member with old | new
        · exact paidLast pair old
        · exact paid' pair new
      · intro pair member
        rcases List.mem_append.mp member with old | new
        · exact delayed pair old
        · exact delayed' pair new
      · intro pair member
        rcases List.mem_append.mp member with old | new
        · exact paying pair old
        · exact paying' pair new
      · rw [List.map_append]
        exact (trace middleElectra).append (trace' electraY)
      · intro called member
        rw [List.append_nil] at member
        obtain ⟨site, inside, read⟩ := sites called member
        exact ⟨site, List.mem_append_left _ inside, read⟩
    | block engine signed due ok =>
      obtain ⟨queue', calls', owned', replay, reserve', assignment', erasure', retired', cover',
        future', _, fresh', trace', sites'⟩ :=
        block x high rounding middleElectra middleEarly delay caps.compounding engine signed due ok
          addedOk queue owned prior.length payments.length calls.length
          (blockAssigned_of_originalDown pre down reserve
            (roundingAt pre (Step.block engine signed due ok) .nil rfl))
          reserve assignment erasure counted
          retired coverM futureM invariant.balancesMatch invariant.exitsOrdered
          pre.registryLifecycle
          (currentEpoch_le_of_chainSteps pre.chainSteps) finite slashedExit fresh
      have counted' := replay.counters counted
      refine ⟨before, owned', queue', payments ++ [], allocations ++ [], calls ++ calls', initialB,
        history.append (by simpa only [Nat.zero_add] using replay), reserve', assignment',
        erasure', by simpa only [List.length_append, List.length_nil, Nat.add_zero] using
          counted', retired', cover', future', fresh', ?_, ?_, ?_, fun electraY => ?_, ?_,
        originalDown_block pre (Step.block engine signed due ok) down
          (effectiveKept_block middleEarly (applySignedBlock_ok ok).2.1)
          replay.counters_original.2.2.1⟩
      · intro pair member
        rw [List.append_nil] at member
        exact paidLast pair member
      · intro pair member
        rw [List.append_nil] at member
        exact delayed pair member
      · intro pair member
        rw [List.append_nil] at member
        exact paying pair member
      · rw [List.map_append]
        exact (trace middleElectra).append trace'
      · intro called member
        rcases List.mem_append.mp member with old | new
        · obtain ⟨site, inside, read⟩ := sites called old
          exact ⟨site, List.mem_append_left _ inside, read⟩
        · obtain ⟨site, inside, read⟩ := sites' called new
          exact ⟨site, List.mem_append_right _ inside, read⟩

/-- From Electra a block deposit keeps every validator and every balance.

It changes no validator, or it appends one new validator.

The new validator has balance 0, effective balance 0, and no activation, exit or withdrawal epoch.

The amount waits in the pending deposits.

The slot, the pending consolidations and the consolidation churn are unchanged. -/
private theorem processDeposit_electra_shape {fork : Fork} {a b : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {dep : Deposit}
    (ok : processDeposit config checks before a dep = .ok b) (matched : BalancesMatch a) :
    b.slot = a.slot ∧
      b.pendingConsolidations electra = a.pendingConsolidations electra ∧
      b.earliestConsolidationEpoch electra = a.earliestConsolidationEpoch electra ∧
      b.consolidationBalanceToConsume electra = a.consolidationBalanceToConsume electra ∧
      ((b.validators.data = a.validators.data ∧ b.balances.data = a.balances.data) ∨
        ∃ w : Validator, b.validators.data = a.validators.data.push w ∧
          b.balances.data = a.balances.data.push 0 ∧ w.effectiveBalance = 0 ∧
          w.slashed = false ∧ w.activationEpoch = FAR_FUTURE_EPOCH ∧
          w.exitEpoch = FAR_FUTURE_EPOCH ∧ w.withdrawableEpoch = FAR_FUTURE_EPOCH) := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, _, rfl | added, rfl⟩ | ⟨early, _⟩
  -- A new key with an invalid signature: nothing but the deposit index changes.
  · exact ⟨rfl, rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  -- A known key: the deposit only joins the pending deposits.
  · exact ⟨rfl, rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  -- A new key with a valid signature: one validator is appended, with no balance.
  · obtain ⟨validators, balances⟩ := addValidatorToRegistry_push added matched
    have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
    simp only [addValidatorToRegistry, altair, ↓reduceDIte, addValidatorToRegistryAltair,
      liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at added
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := added
    refine ⟨rfl, rfl, rfl, rfl, .inr ⟨_, validators, balances, ?_, rfl, rfl, rfl, rfl⟩⟩
    -- The new validator is built from an amount of 0.
    apply UInt64.toNat_inj.mp
    simp [getValidatorFromDeposit, Uint64.toNat_min]
  · exact absurd (Nat.lt_of_lt_of_le early electra) (Nat.lt_irrefl _)

/-- One block deposit from Electra replays as its recorded event, with the same queue and ownership.

Its credit is 0: the amount waits in the pending deposits.

Every existing validator and balance is unchanged.

A validator the deposit appends has balance 0 and effective balance 0.

So every reserve and cover clause holds for it with no token. -/
theorem operationReplay_deposit {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork) {before : fork < .hegota}
    (dep : Deposit) (a b : BeaconState preset fork) (credit debit : Nat)
    (_limits : (pure (if fork < .pectra then dep.data.amount.toNat else 0, 0) :
      Except TransitionError (Nat × Nat)) = .ok (credit, debit))
    (ok : processDeposit config checks before a dep = .ok b)
    (_bounded : (⟨.deposits, ⟨fork, a⟩, ⟨fork, b⟩, credit, debit⟩ : BalanceEvent preset).credits ≤
      credit) :
    OperationReplay (config := config) (checks := checks) x high rounding electra a b
        [⟨.deposits, ⟨fork, a⟩, ⟨fork, b⟩, credit, debit⟩] [] ∧
      getCurrentEpoch b = getCurrentEpoch a ∧
      (BalancesMatch a → ExitsOrdered a →
        RegistryLifecycle x.state a →
        BalancesMatch b ∧ ExitsOrdered b ∧
          RegistryLifecycle x.state b) := by
  have step := frame_processDeposit ok
  have epoch : getCurrentEpoch b = getCurrentEpoch a := by
    simp only [getCurrentEpoch, step.slot]
  have lifeStep := registryLifecycle_processDeposit ok
  refine ⟨?_, epoch, fun matched exits life =>
    ⟨step.balancesMatch matched, step.exitsOrdered exits, life.trans lifeStep⟩⟩
  intro queue owned eventPosition paymentPosition callPosition reserve assignment erasure _
    retired cover future matched _ life _ _ slashed fresh
  obtain ⟨_, pending, earliest, consume, shape⟩ := processDeposit_electra_shape electra ok matched
  have sizes : a.balances.data.size = a.validators.data.size := matched
  -- Every existing index keeps its validator and its balance.
  have keptValidator : ∀ i, i < a.validators.data.size →
      b.validators.data[i]? = a.validators.data[i]? := by
    intro i inside
    rcases shape with ⟨same, _⟩ | ⟨w, pushed, _⟩
    · rw [same]
    · rw [pushed]
      simp [Array.getElem?_push, Nat.ne_of_lt inside]
  have keptBalance : ∀ i, i < a.validators.data.size →
      actualBalanceAt (⟨fork, b⟩ : ForkedBeaconState preset) i = actualBalanceAt ⟨fork, a⟩ i := by
    intro i inside
    simp only [actualBalanceAt]
    rcases shape with ⟨_, same⟩ | ⟨w, _, pushed, _⟩
    · rw [same]
    · have apart : i ≠ a.balances.data.size := by omega
      rw [pushed]
      simp [Array.getElem?_push, apart]
  -- An appended index has no balance, no effective balance and no flag.
  have appended : ∀ j w, a.validators.data.size ≤ j → b.validators.data[j]? = some w →
      w.effectiveBalance = 0 ∧ w.slashed = false ∧ w.activationEpoch = FAR_FUTURE_EPOCH ∧
        actualBalanceAt (⟨fork, b⟩ : ForkedBeaconState preset) j = 0 := by
    intro j w outside found
    rcases shape with ⟨same, _⟩ | ⟨v, pushed, balances, effective, clean, activationFar, _⟩
    · rw [same, Array.getElem?_eq_none outside] at found
      cases found
    · rw [pushed, Array.getElem?_push] at found
      split at found
      · rename_i last
        cases found
        refine ⟨effective, clean, activationFar, ?_⟩
        subst last
        simp [actualBalanceAt, balances, ← sizes]
      · rw [Array.getElem?_eq_none outside] at found
        cases found
  have registry : ∃ added : Array Validator,
      b.validators.data = a.validators.data ++ added := by
    rcases shape with ⟨same, _⟩ | ⟨w, pushed, _⟩
    · exact ⟨#[], by rw [same, Array.append_empty]⟩
    · exact ⟨#[w], by rw [pushed, Array.push_eq_append]⟩
  have balancesLe : ∀ i, actualBalanceAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt ⟨fork, a⟩ i + 0 := by
    intro i
    by_cases inside : i < a.validators.data.size
    · rw [keptBalance i inside]
      exact Nat.le_refl _
    · simp only [actualBalanceAt]
      rcases shape with ⟨_, same⟩ | ⟨w, _, pushed, _⟩
      · rw [same]
        exact Nat.le_refl _
      · rw [pushed, Array.getElem?_push]
        split <;> simp
  -- A validator at `x` was in the registry before the deposit.
  have appendedFresh : ∀ j w, a.validators.data.size ≤ j →
      b.validators.data[j]? = some w → x.state.validators.data[j]? = none :=
    fun j _ outside _ => Array.getElem?_eq_none (Nat.le_trans life.size_le outside)
  have reserveA := reserveCut_balance_append (x := x) (high := high) (before := owned)
    (after := owned) (growth := fun _ => 0) (u := ⟨fork, a⟩) (v := ⟨fork, b⟩) rfl registry
    balancesLe reserve.1 rfl rfl (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _) appendedFresh
    (fun j w outside _ member => by
      obtain ⟨v, found, _⟩ := retired j member
      rw [Array.getElem?_eq_none outside] at found
      cases found)
    (fun j w outside found => by
      obtain ⟨effective, _, _, balance⟩ := appended j w outside found
      simp [effectiveAt, found, effective, balance])
    (fun j w outside found _ _ => by
      obtain ⟨effective, _, _, _⟩ := appended j w outside found
      simp [effectiveAt, found, effective])
    reserve
  have reserveT : ReserveCut x high ⟨fork, b⟩ (getCurrentEpoch b) (queue.map (·.entry)) owned := by
    rw [epoch]
    exact reserveA
  have queueSame : pendingQueue (⟨fork, b⟩ : ForkedBeaconState preset) =
      pendingQueue ⟨fork, a⟩ := by
    simp only [pendingQueue, electra, ↓reduceDIte, pending]
  have erasureT : QueueErasure queue (pendingQueue ⟨fork, b⟩) := by
    rw [queueSame]
    exact erasure
  have identity : OwnedFrame owned owned :=
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl, Finset.Subset.refl _, rfl,
      fun _ => Nat.le_refl _⟩
  have notTransfer : (⟨.deposits, ⟨fork, a⟩, ⟨fork, b⟩, credit, debit⟩ :
      BalanceEvent preset).source ≠ .consolidations := by
    intro same
    cases same
  have replay := ReservedReplay.singleton_nonconsolidation
    (e := ⟨.deposits, ⟨fork, a⟩, ⟨fork, b⟩, credit, debit⟩) (eventPosition := eventPosition)
    (paymentPosition := paymentPosition) (callPosition := callPosition) notTransfer
    (reservedFrame_refl (config := config) (checks := checks) reserve assignment erasure)
    (by
      unfold TagEvent
      exact ⟨erasure, erasureT, .inl ⟨notTransfer, rfl, rfl, rfl, rfl⟩⟩)
    (by
      unfold ReservedEvent OwnedEvent
      refine ⟨?_, assignment, assignment, ?_⟩
      · split
        · exact absurd ‹_› notTransfer
        · exact ⟨rfl, rfl, .inr identity⟩
      · split
        · exact absurd ‹_› notTransfer
        · exact ⟨reserve, reserveT⟩)
  refine ⟨queue, [], owned, replay, reserveT, assignment, erasureT,
    retired.lifecycle lifeStep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- An existing validator reads as before; an appended one has nothing to cover.
  · intro i v found clean notExited current
    by_cases inside : i < a.validators.data.size
    · rw [keptValidator i inside] at found
      rw [keptBalance i inside]
      exact cover i v found clean notExited (by rw [← epoch]; exact current)
    · obtain ⟨_, _, _, balance⟩ := appended i v (Nat.le_of_not_lt inside) found
      rw [balance, Nat.zero_min]
      exact Nat.zero_le _
  · intro i v found later clean notExited
    by_cases inside : i < a.validators.data.size
    · have effective : effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i =
          effectiveAt ⟨fork, a⟩ i := by
        simp only [effectiveAt, keptValidator i inside]
      rw [keptValidator i inside] at found
      rw [effective]
      exact future i v found (by rw [← epoch]; exact later) clean notExited
    · obtain ⟨zero, _, _, _⟩ := appended i v (Nat.le_of_not_lt inside) found
      simp [effectiveAt, found, zero]
  · intro i v found flag
    by_cases inside : i < a.validators.data.size
    · rw [keptValidator i inside] at found
      exact slashed i v found flag
    · obtain ⟨_, clean, _, _⟩ := appended i v (Nat.le_of_not_lt inside) found
      rw [clean] at flag
      cases flag
  · intro tag member n tagged
    obtain ⟨v, found, exit, assigned⟩ := fresh tag member n tagged
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨v, by rw [keptValidator _ inside]; exact found, exit, assigned⟩
  · rw [earliest, consume]
    exact .nil _ _
  · intro called member
    cases member

end

/-- The run's reserved history and its counters give the selected inputs. -/
private theorem selectedInputs_of_run
    (slotStep : SlotStepReplay (preset := preset) (config := config) (checks := checks))
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    {g x y : ForkedBeaconState preset} :
    SelectedInputs (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail high supported twoSlots events replayed electra
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    obtain ⟨_, _, _, _, _, _, guard⟩ := id supported
    obtain ⟨_, _, _, _, _, _, _, _, _, delayTwo, _⟩ := id guard
    omega
  -- The rounding ledger of the branch marks every key whose exit follows a first drop.
  obtain ⟨ledger, -⟩ := (LedgerCuts.ofStops tail fun i => Classical.choice
    (Stop.exists tail i)).roundLedger_closed_electra shared supported electra twoSlots
  obtain ⟨_, _, _, _, _, _, _, history, _, _, _, _, _, _, _, _, _, _, paying, _⟩ :=
    reservedReplay_run shared tail high supported twoSlots electra
      (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
      (fun pre step rest split i v w before after unset assigned reference drop => by
        simp [ledger.sourceFalling_of_firstDown shared supported delay pre step rest split i v w
          before after unset assigned reference drop])
      slotStep block replayed
  exact selectedInputs_of_history shared tail supported replayed electra history paying

/-- The selected charges of a run fit the initial consolidation carry and the moved flow.

The given calls are the run's own calls, by the uniqueness of the tag replay. -/
private theorem selected_capacity_of_run
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (electra : .pectra ≤ x.fork)
    {selected : List SelectedCharge} {payments : List (Payment preset)} {tags : List TaggedEntry}
    (chosen : SelectedPayments selected payments tags)
    {final consumed : List TaggedEntry} {calls : List (IndexedDepartureCall preset config)}
    (fresh : FreshPaymentCoverage (config := config) events
      (initialTags (x.state.pendingConsolidations electra).data.toList)
      final consumed tags payments calls)
    (unique : FreshTags (config := config) (consumed ++ final) calls) :
    SelectedCapacity (config := config) x high selected := by
  obtain ⟨genesis, _, caps, aligned, early, endEpoch, guard⟩ := id supported
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, _, delayTwo, _⟩ := id guard
    omega
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have electraY : .pectra ≤ y.fork := Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
  obtain ⟨ledger, -⟩ := (LedgerCuts.ofStops tail fun i => Classical.choice
    (Stop.exists tail i)).roundLedger_closed_electra shared supported electra twoSlots
  obtain ⟨_, _, _, runPayments, _, runCalls, _, history, _, _, _, _, _, _, _, _, paidBy, delayed,
      _, trace, sites, _⟩ :=
    reservedReplay_run shared tail high supported twoSlots electra
      (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
      (fun pre step rest split i v w before after unset assigned reference drop => by
        simp [ledger.sourceFalling_of_firstDown shared supported delay pre step rest split i v w
          before after unset assigned reference drop])
      reservedReplay_slotStep block replayed
  -- The given replay is the run's replay.
  obtain ⟨runConsumed, _, runReplay, runPaid, -⟩ := history.counters_original.2.2.2.2.2.2.2
  obtain ⟨allPaid, replay, tagsEq, paymentsEq⟩ := fresh
  obtain ⟨-, consumedEq, paidEq, callsEq⟩ := replay.unique runReplay
  rw [← callsEq] at trace sites
  rw [← consumedEq, ← paidEq] at runPaid
  rw [← paidEq] at paidBy delayed
  let isFresh : TaggedEntry × Payment preset → Bool := fun pair =>
    pair.1.tag.isFresh
  have freshPairs : ∀ pair ∈ allPaid.filter isFresh, pair ∈ allPaid ∧
      ∃ n, pair.1.tag = .fresh n := by
    intro pair member
    obtain ⟨inside, picked⟩ := List.mem_filter.mp member
    refine ⟨inside, ?_⟩
    cases kind : pair.1.tag with
    | fresh n => exact ⟨n, rfl⟩
    | initial p => simp [isFresh, kind] at picked
  -- Each call starts at or after `x` and reads a consolidation churn within the moved flow.
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  have firsts : DepartureCallsFrom (getCurrentEpoch x.state).toNat calls := by
    intro called member
    obtain ⟨site, inside, first, _⟩ := sites called member
    have later := UInt64.le_iff_toNat_le.mp
      (consolidationSite_epoch_total tail electra early site inside).2.2.1
    have value := (computeActivationExitEpoch_ok_iff.mp first).2
    omega
  have rates : ∀ called ∈ calls,
      called.call.rate.toNat ≤ consolidationFlowAt (config := config) x high 0 := by
    intro called member
    obtain ⟨site, inside, _, computed⟩ := sites called member
    obtain ⟨u, _, step, contained, _, same⟩ := consolidationSite_rate tail early site inside
    have read := same _ computed
    obtain ⟨_, _, _, uEarly, epochOrder⟩ := Run.contains_step_facts contained early
    obtain ⟨total, totalRead⟩ := consolidationChurnLimit_total uEarly read
    have index : (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat ≤
        driftHorizon x high + 1 := by
      unfold driftHorizon
      omega
    have ceiling := (stepTotal_le_ceiling shared genesis tail electra early high endEpoch guard
      aligned unit
      (fun head headEarly within found ok => otherCredit_le_allowance_electra shared genesis head
        caps aligned electra headEarly twoSlots high within guard ok)
      (fun head headEarly before total ok => floor_all_runs_electra shared genesis
        supported.2.1 caps aligned guard electra twoSlots head headEarly (by omega) total ok)
      step contained totalRead).trans (ceilingAt_mono electra high index)
    have bound := (consolidationChurnLimit_le uEarly totalRead read).trans
      (consolidationChurn_mono ceiling)
    simpa only [consolidationFlowAt, consolidationFlow, zero, Nat.lt_irrefl, ↓reduceIte] using bound
  -- The paid tags are consumed, so the selected charges inject into the calls.
  have paid : tags.Sublist consumed := by
    rw [tagsEq]
    exact ((List.filter_sublist).map _).trans runPaid
  have injection := selected_injection unique paid chosen
  -- Each fresh payment waited the delay and pays by the end of the branch.
  have cutoff : Cutoff (config := config) x high selected := by
    refine selected_cutoff endEpoch chosen (fun i tag v found read => ?_)
      (fun p member => ?_)
    · subst tagsEq paymentsEq
      have inside : i.val < (allPaid.filter isFresh).length := by simpa using i.isLt
      obtain ⟨member, n, kind⟩ := freshPairs _ (List.getElem_mem inside)
      change ((allPaid.filter isFresh).map Prod.fst)[i.val]? = some tag at found
      change ((allPaid.filter isFresh).map Prod.snd)[i.val].before.state.validators.data[
        ((allPaid.filter isFresh).map Prod.snd)[i.val].source]? = some v at read
      rw [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some,
        Option.some.injEq] at found
      subst found
      obtain ⟨w, wRead, wait⟩ := delayed _ member n kind
      rw [List.getElem_map, wRead, Option.some.injEq] at read
      subst read
      exact wait
    · rw [paymentsEq] at member
      obtain ⟨pair, inside, rfl⟩ := List.mem_map.mp member
      exact paidBy _ (freshPairs _ inside).1
  exact selected_capacity electra (trace electraY) firsts rates injection cutoff

section

open Cryptography.Bls Uint64

/-- The selected-release statement from the run's reserved replay.

The run replay rounds with the ledger's source-falling keys.

The given fresh coverage replays the same tags.

A tag replay is determined by its events, start position and initial queue.

So its queue, calls and payments are the replay's own.

The deposit funding and the selected capacity are taken as hypotheses. -/
private theorem selectedReleaseProducer_of_run {g x y : ForkedBeaconState preset}
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    (deposits : ∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → .pectra ≤ x.fork →
      ∀ events, tail.balanceEvents high = .ok events →
        (events.map funding_deposit_credit).sum + fundingCarry y ≤
          fundingCarry x +
              ((List.range (driftHorizon x high + 1)).map
                (exitFlowAt (config := config) x high)).sum)
    (capacity : ∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
      ∀ events, tail.balanceEvents high = .ok events →
      ∀ electra : .pectra ≤ x.fork, ∀ selected payments tags,
      ActualPaymentCoverage events payments (x.state.pendingConsolidations electra).data.toList →
      SelectedPayments (preset := preset) selected payments tags →
      ∀ final consumed calls,
      FreshPaymentCoverage (config := config) events
        (initialTags (x.state.pendingConsolidations electra).data.toList)
        final consumed tags payments calls →
      FreshTags (config := config) (consumed ++ final) calls →
        SelectedCapacity (config := config) x high selected) :
    SelectedReleaseProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail high supported twoSlots events replayed electra selected payments tags actual
    chosen final consumed calls coverage freshTags ledger
  obtain ⟨genesis, _, caps, aligned, early, endEpoch, guard⟩ := id supported
  have delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, _, delay, _⟩ := id guard
    exact delay
  have delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by omega
  -- The run replay, rounding each source-falling key by one increment.
  obtain ⟨before, after, queue, allPayments, allAllocations, runCalls, initial, history, cut,
    _⟩ := reservedReplay_run shared tail high supported twoSlots electra
      (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
      (fun pre step rest split i v w found next unset assigned reference drop =>
        ite_eq_left (ledger.sourceFalling_of_firstDown shared supported delay pre step rest split
          i v w found next unset assigned reference drop))
      reservedReplay_slotStep block replayed
  -- The given coverage replays the same tags, so it names the replay's queue, calls and payments.
  obtain ⟨_, _, _, _, _, _, _, _, _, tagReplay, _⟩ := history.counters_original
  obtain ⟨allPaid, coverReplay, named⟩ := coverage
  obtain ⟨tagsEq, paymentsEq⟩ := named
  obtain ⟨rfl, _, rfl, rfl⟩ := TagReplay.unique tagReplay coverReplay
  have lengths := history.paired_rounds.length_eq
  let pairs := (allPayments.zip allAllocations).filter fun pair =>
    pair.1.1.tag.isFresh
  have payEq : payments = pairs.map (fun pair => pair.1.2) := by
    rw [paymentsEq]
    exact (zip_filter_fst_map _ Prod.snd _ _ lengths).symm
  have tagEq : tags = pairs.map (fun pair => pair.1.1) := by
    rw [tagsEq]
    exact (zip_filter_fst_map _ Prod.fst _ _ lengths).symm
  obtain ⟨partition, rounds, roundSum, baselineSum⟩ :=
    history.release_rounding ledger (allocations := pairs.map Prod.snd) ⟨payEq, rfl, tagEq⟩
      chosen
  obtain ⟨initialEq, creditBound, releasesEq, total⟩ := ownership_counts initial history
  have deposited := deposits shared tail high supported twoSlots electra events replayed
  have issued := issuance_electra shared tail high supported twoSlots electra replayed
  have funding : CumulativeFunding (config := config) x y high events selected
      (pairs.map Prod.snd) before after :=
    ⟨initialEq, creditBound, releasesEq, deposited, issued,
      otherCredit_le_allowanceAt_electra shared genesis tail caps aligned electra early twoSlots
        high endEpoch guard replayed issued (Nat.le_of_add_right_le deposited),
      capacity shared tail high supported twoSlots events replayed electra selected payments tags
        actual chosen queue consumed runCalls ⟨allPayments, coverReplay, tagsEq, paymentsEq⟩
        freshTags,
      by rw [releasesEq]; exact baselineSum, total⟩
  have demand := endpointDemand_of_reserveCut (shared.append tail) genesis early cut
  obtain ⟨tokens, terminal⟩ := terminalAllocation_of_demand cut.1 demand
  exact ⟨pairs.map Prod.snd, before, after, tokens, initial,
    ⟨allPayments, allAllocations, history, payEq, rfl⟩, funding, terminal,
    newCohortAllocation_electra shared tail high supported twoSlots electra events replayed ledger
      terminal,
    ScheduledAllocation.ofReads tail high, demand, cumulativeFunding_bound electra initial funding,
    partition, rounds, roundSum, baselineSum⟩

/-- The release from the block replay and the deposit funding bound.

Its selected capacity holds, since the run's selected charges fit the carry and flow. -/
private theorem releaseProducer_of_block
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    (deposits : ∀ g x y : ForkedBeaconState preset,
      (∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
        Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → .pectra ≤ x.fork →
        ∀ events, tail.balanceEvents high = .ok events →
          (events.map funding_deposit_credit).sum + fundingCarry y ≤
            fundingCarry x +
              ((List.range (driftHorizon x high + 1)).map
                    (exitFlowAt (config := config) x high)).sum))
    (g x y : ForkedBeaconState preset) :
    SelectedReleaseProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) :=
  selectedReleaseProducer_of_run block (deposits _ _ _)
    (fun shared tail high supported twoSlots _ replayed electra _ _ _ _ chosen _ _ _ fresh
        unique =>
      selected_capacity_of_run block shared tail high supported twoSlots replayed electra
        chosen fresh unique)

/-- The headline from the block replay and the deposit funding bound.

The selected inputs come from the slot and block replays, and the release from its assembly.

The release's selected capacity holds, since the run's selected charges fit the carry and flow. -/
theorem headline_of_block
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    (deposits : ∀ g x y : ForkedBeaconState preset,
      (∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
        Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → .pectra ≤ x.fork →
        ∀ events, tail.balanceEvents high = .ok events →
          (events.map funding_deposit_credit).sum + fundingCarry y ≤
            fundingCarry x +
              ((List.range (driftHorizon x high + 1)).map
                    (exitFlowAt (config := config) x high)).sum)) :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) :=
  headline_ledger (fun _ _ _ => selectedInputs_of_run reservedReplay_slotStep block)
    (releaseProducer_of_block block deposits)

/-- The drift of a supported branch from the block replay and the deposit funding bound.

The inputs are those of the headline. -/
theorem stateProducer_of_block
    (block : BlockReplay (preset := preset) (config := config) (checks := checks))
    (deposits : ∀ g x y : ForkedBeaconState preset,
      (∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
        Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → .pectra ≤ x.fork →
        ∀ events, tail.balanceEvents high = .ok events →
          (events.map funding_deposit_credit).sum + fundingCarry y ≤
            fundingCarry x +
              ((List.range (driftHorizon x high + 1)).map
                    (exitFlowAt (config := config) x high)).sum))
    (g x y : ForkedBeaconState preset) :
    StateProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) :=
  stateProducer_ledger (fun _ _ _ => selectedInputs_of_run reservedReplay_slotStep block)
    (releaseProducer_of_block block deposits) g x y

end

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
