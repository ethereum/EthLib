module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Reserved.Operations

/-!
# The reserved replay of an epoch

The pending consolidations and the other stages of an epoch keep the reserve cut.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-- A source due at `next` is never supported at `next` or later.

Its exit is before every such epoch, so it is active at neither that epoch nor the one before.

The epoch before does not wrap: an epoch after an exit is at least one. -/
private theorem pendingTransfer_sourceGone {w : Validator} {next : Epoch}
    (ordered : w.exitEpoch ≤ w.withdrawableEpoch)
    (delay : w.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (due : w.withdrawableEpoch ≤ next) (finite : next < FAR_FUTURE_EPOCH) :
    ∀ epoch, next ≤ epoch → ¬ SupportedAt epoch w := by
  intro epoch later supported
  have laterNat := UInt64.le_iff_toNat_le.mp later
  have exited := UInt64.lt_iff_toNat_lt.mp
    (due_exit_before (current := epoch) finite ordered delay due (by omega))
  rcases supported.2 with now | before
  · simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt] at now
    omega
  · -- The epoch is after the exit, so it is at least one and `epoch - 1` does not wrap.
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt] at before
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at before
    simp only [UInt64.reduceToNat] at before
    omega
/-- Dropping the head of the suffix keeps the reserve cut.

Tail membership implies membership in the original suffix.

So each tail obligation follows from the original cut.

Absence from the original suffix implies absence from the tail. -/
private theorem reserveCut_drop_head {x : ForkedBeaconState preset} {fork : Fork}
    {s : BeaconState preset fork} {high : Nat} {next : Epoch} {head : PendingConsolidation}
    {tail : List PendingConsolidation} {owned : Ownership}
    (reserve : ReserveCut x high ⟨fork, s⟩ next (head :: tail) owned) :
    ReserveCut x high ⟨fork, s⟩ next tail owned := by
  have relevant : ∀ i, FundingRelevant ⟨fork, s⟩ next tail i →
      FundingRelevant ⟨fork, s⟩ next (head :: tail) i := by
    rintro i ⟨validator, located, rest⟩
    refine ⟨validator, located, rest.imp_right (Or.imp_right ?_)⟩
    rintro ⟨q, member, same⟩
    exact ⟨q, List.mem_cons_of_mem _ member, same⟩
  obtain ⟨valid, wasRetired, original, reference, scheduled, pending, queued, idle,
    activePending, endpoint⟩ := reserve
  refine ⟨valid, ?_, original, fun i ref notRetired support =>
    reference i ref notRetired (relevant i support), scheduled,
    fun i initial notRetired support => pending i initial notRetired (relevant i support),
    fun entry member => queued entry (List.mem_cons_of_mem _ member), ?_,
    fun i initial validator old located current active notRetired support =>
      activePending i initial validator old located current active notRetired
        (relevant i support), endpoint⟩
  · intro i member validator located
    obtain ⟨unsupported, absent⟩ := wasRetired i member validator located
    exact ⟨unsupported, fun ⟨q, member, same⟩ =>
      absent ⟨q, List.mem_cons_of_mem _ member, same⟩⟩
  · intro i validator located notRef notPending quiet support
    exact idle i validator located notRef notPending quiet
      (support.imp_right (Or.imp_right fun ⟨⟨q, member, same⟩, outside⟩ =>
        ⟨⟨q, List.mem_cons_of_mem _ member, same⟩, outside⟩))

/-- Dropping the head of the queue keeps the assignment cut. -/
private theorem assignmentCut_drop_head {rounding : Nat → Nat} {tag : TaggedEntry}
    {tags : List TaggedEntry} {owned : Ownership}
    (cut : AssignmentCut rounding (tag :: tags) owned) : AssignmentCut rounding tags owned :=
  assignmentCut_transport cut (fun _ => Nat.le_refl _) (List.sublist_cons_self _ _)

theorem OwnedInitial.retiredActivated {x : ForkedBeaconState preset}
    (initial : OwnedInitial x high owned) : RetiredActivated x.state owned.retired := by
  intro i member
  rw [initial.2.1] at member
  exact False.elim (Finset.notMem_empty i member)

private theorem RetiredActivated.transfer {p : Payment preset}
    (prior : RetiredActivated p.before.state before.retired)
    (life : RegistryLifecycle p.before.state p.after.state)
    (v : Validator) (found : p.before.state.validators.data[p.source]? = some v)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (transfer : OwnedTransfer position p allocation before after) :
    RetiredActivated p.after.state after.retired := by
  rw [transfer.source_retirement.2]
  exact (prior.insert p.source v found assigned).lifecycle life

/-- An owned transfer keeps the future cover when its source is not guarded.

The registry stays, so every effective balance stays.

The target gains the whole payment at its endpoint, and every other key keeps its endpoint tokens.

The source loses its tokens, so `sourceGone` excludes it from the guard. -/
private theorem futureCover_transfer {x u v : ForkedBeaconState preset} {position : Nat}
    {p : Payment preset} {allocation : OwnedRelease} {before after : Ownership}
    (transfer : OwnedTransfer position p allocation before after)
    (apart : p.source ≠ p.target)
    (registry : v.state.validators.data = u.state.validators.data)
    (epochs : getCurrentEpoch v.state = getCurrentEpoch u.state)
    (sourceGone : ∀ w, u.state.validators.data[p.source]? = some w →
      getCurrentEpoch u.state < w.activationEpoch → w.slashed = false →
      getCurrentEpoch x.state < w.exitEpoch → False)
    (cover : FutureEffectiveCover x u before) :
    FutureEffectiveCover x v after := by
  have targetEndpoint := (ownedTransfer_held transfer apart).2.1
  intro i w found later clean notExited
  have foundU : u.state.validators.data[i]? = some w := registry ▸ found
  have laterU : getCurrentEpoch u.state < w.activationEpoch := epochs ▸ later
  have was := cover i w foundU laterU clean notExited
  have effective : effectiveAt v i = effectiveAt u i := by simp only [effectiveAt, registry]
  rw [effective]
  by_cases source : i = p.source
  · subst source
    exact (sourceGone w foundU laterU clean notExited).elim
  by_cases target : i = p.target
  · subst target
    omega
  · rw [ownedTransfer_endpoint_other transfer apart source target]
    exact was

/-- A paid pending consolidation keeps the future cover.

A due source has an assigned exit at most `next`, and its activation is at most its exit.

So it is not still to activate.

The same arithmetic that excludes it from the endpoint cover applies. -/
private theorem futureCover_pendingTransfer {x : ForkedBeaconState preset} {fork : Fork}
    {u d t : BeaconState preset fork} {c : PendingConsolidation} {w : Validator}
    {b : Gwei} {next : Epoch} {position : Nat} {allocation : OwnedRelease}
    {before after : Ownership}
    (found : getValidator u c.sourceIndex = .ok w)
    (debited : decreaseBalance u c.sourceIndex (min b w.effectiveBalance) = .ok d)
    (credited : increaseBalance d c.targetIndex (min b w.effectiveBalance) = .ok t)
    (transfer : OwnedTransfer position
      ⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b w.effectiveBalance).toNat, next.toNat,
        ⟨fork, u⟩, ⟨fork, t⟩⟩ allocation before after)
    (apart : c.sourceIndex ≠ c.targetIndex)
    (nextOk : Uint64.addChecked (getCurrentEpoch u) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered u)
    (activation : ∀ v ∈ u.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (delay : ∀ (i : Nat) (v : Validator), u.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : w.withdrawableEpoch ≤ next)
    (cover : FutureEffectiveCover x ⟨fork, u⟩ before) :
    FutureEffectiveCover x ⟨fork, t⟩ after := by
  have foundU := getValidator_eq_ok_iff.mp found
  have apartNat : c.sourceIndex.toNat ≠ c.targetIndex.toNat :=
    fun same => apart (UInt64.toNat_inj.mp same)
  obtain ⟨validators, slot, _, _⟩ := pendingTransfer_balances debited credited apartNat
  refine futureCover_transfer (u := ⟨fork, u⟩) transfer apartNat
    (congrArg (·.data) validators) (by simp only [getCurrentEpoch, slot]) ?_ cover
  intro v foundV later _ _
  change u.validators.data[c.sourceIndex.toNat]? = some v at foundV
  rw [foundU] at foundV
  cases foundV
  -- Still to activate means the current epoch is before the activation, so before the exit.
  have covered := UInt64.le_of_lt
    (UInt64.lt_of_lt_of_le later (activation w (Array.mem_of_getElem? foundU)))
  exact consolidation_sourceGone twoSlots nextOk (exits w (Array.mem_of_getElem? foundU))
    (delay _ w foundU) due covered

/-- The effective-balance updates change only effective balances.

Each new value is the old value, or at most the balance and the largest effective balance. -/
private theorem processEffectiveBalanceUpdates_lookup {fork : Fork}
    {u v : BeaconState preset fork} (ok : processEffectiveBalanceUpdates u = .ok v)
    (matched : BalancesMatch u) :
    ∀ (i : Nat) (w : Validator), v.validators.data[i]? = some w → ∃ w₀ balance effective,
      u.validators.data[i]? = some w₀ ∧ u.balances.data[i]? = some balance ∧
        w = { w₀ with effectiveBalance := effective } ∧
        (effective = w₀.effectiveBalance ∨
          effective ≤ balance ∧ effective ≤ withdrawalMaxEffectiveBalance preset fork w₀) := by
  have sizes := (sameSizes_processEffectiveBalanceUpdates ok).1
  intro i w found
  have insideV := (Array.getElem?_eq_some_iff.mp found).1
  have inside : i < u.validators.data.size := by omega
  have foundU := Array.getElem?_eq_getElem inside
  have insideB : i < u.balances.data.size := by
    unfold BalancesMatch at matched
    omega
  have owned := Array.getElem?_eq_getElem insideB
  obtain ⟨effective, updated, cases⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance ok foundU owned
  rw [found, Option.some.injEq] at updated
  exact ⟨_, _, _, foundU, owned, updated, cases⟩

/-- The effective-balance updates keep the endpoint cover.

They keep the balances, the slot and every field the cover reads. -/
private theorem endpointCover_effective {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (ok : processEffectiveBalanceUpdates u = .ok v) (matched : BalancesMatch u)
    (cover : EndpointCoverAll x ⟨fork, u⟩ o) : EndpointCoverAll x ⟨fork, v⟩ o := by
  have frame := processEffectiveBalanceUpdates_frame ok
  have balances := processEffectiveBalanceUpdates_balances ok
  have epoch : getCurrentEpoch v = getCurrentEpoch u := by
    rw [frame]
    rfl
  apply endpointCover_mono (u := ⟨fork, u⟩) ?_ (fun _ => Nat.le_refl _) cover
  intro i w found clean notExited current
  obtain ⟨w₀, _, e, foundU, _, rfl, _⟩ := processEffectiveBalanceUpdates_lookup ok matched i w found
  refine ⟨w₀, foundU, clean, notExited, epoch ▸ current, rfl, ?_⟩
  have balanceEq : actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i =
      actualBalanceAt ⟨fork, u⟩ i := by
    simp only [actualBalanceAt, balances]
  have capEq : withdrawalMaxEffectiveBalance preset fork
      { w₀ with effectiveBalance := e } =
      withdrawalMaxEffectiveBalance preset fork w₀ := rfl
  show min _ (withdrawalMaxEffectiveBalance preset fork _).toNat ≤ _
  rw [balanceEq, capEq]

/-- The effective-balance updates keep the future cover, given the endpoint cover before them. -/
private theorem futureCover_effective {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (ok : processEffectiveBalanceUpdates u = .ok v) (matched : BalancesMatch u)
    -- A validator still to activate has not reached its exit.
    --
    -- That holds since its activation is at most its exit.
    (activation : ∀ w ∈ u.validators.data, w.activationEpoch ≤ w.exitEpoch)
    -- The endpoint cover bounds a new effective balance, which is at most the balance and the cap.
    (endpoint : EndpointCoverAll x ⟨fork, u⟩ o)
    (cover : FutureEffectiveCover x ⟨fork, u⟩ o) : FutureEffectiveCover x ⟨fork, v⟩ o := by
  -- An effective balance that stays is covered as before.
  --
  -- A new one is at most the balance and the largest effective balance.
  have frame := processEffectiveBalanceUpdates_frame ok
  have epoch : getCurrentEpoch v = getCurrentEpoch u := by
    rw [frame]
    rfl
  intro i w found later clean notExited
  obtain ⟨w₀, balance, e, foundU, owned, rfl, cases⟩ :=
    processEffectiveBalanceUpdates_lookup ok matched i w found
  have effective : effectiveAt (⟨fork, v⟩ : ForkedBeaconState preset) i = e.toNat := by
    simp [effectiveAt, found]
  have laterU : getCurrentEpoch u < w₀.activationEpoch := epoch ▸ later
  rw [effective]
  rcases cases with same | ⟨lowBalance, lowCap⟩
  · have was := cover i w₀ foundU laterU clean notExited
    have old : effectiveAt (⟨fork, u⟩ : ForkedBeaconState preset) i =
        w₀.effectiveBalance.toNat := by simp [effectiveAt, foundU]
    rw [same]
    dsimp only
    omega
  · have current : getCurrentEpoch u ≤ w₀.exitEpoch := UInt64.le_of_lt
      (UInt64.lt_of_lt_of_le laterU (activation w₀ (Array.mem_of_getElem? foundU)))
    have bound := endpoint i w₀ foundU clean notExited current
    have actual : actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) i = balance.toNat := by
      simp [actualBalanceAt, owned]
    have toBalance := UInt64.le_iff_toNat_le.mp lowBalance
    have toCap := UInt64.le_iff_toNat_le.mp lowCap
    change min _ (withdrawalMaxEffectiveBalance preset fork w₀).toNat ≤ _ at bound
    rw [actual] at bound
    dsimp only
    omega

/-- A successful pending-consolidation pass over a tagged queue is a tagged pass.

Its payments carry the reserve cut, the ownership and both covers. -/
private theorem TaggedPass.reserved_of_pass {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {next : Epoch} {eventPosition position : Nat}
    {s : BeaconState preset fork} {queue : List TaggedEntry}
    {result : BeaconState preset fork × Nat} {before : Ownership}
    (passed : passPendingConsolidations next s (queue.map (·.entry)) = .ok result)
    (reserve : ReserveCut x high ⟨fork, s⟩ next (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before)
    (counters : OwnershipBefore eventPosition position before)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (finite : next < FAR_FUTURE_EPOCH)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered s)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (delay : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (caps : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      before.original tag.entry.sourceIndex.toNat = 0)
    (cover : EndpointCoverAll x ⟨fork, s⟩ before)
    (future : FutureEffectiveCover x ⟨fork, s⟩ before)
    (retired : RetiredActivated s before.retired)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ suffix consumed payments allocations after,
      TaggedPass next s queue result.1 suffix consumed payments ∧ consumed.length = result.2 ∧
      ReservedPayments x high rounding next position s queue result.1 suffix payments allocations
        before after ∧
      ReserveCut x high ⟨fork, result.1⟩ next (suffix.map (·.entry)) after ∧
      AssignmentCut rounding suffix after ∧
      OwnershipBefore eventPosition (position + payments.length) after ∧
      EndpointCoverAll x ⟨fork, result.1⟩ after ∧ RetiredActivated result.1 after.retired ∧
      OwnedPayments position (payments.map Prod.snd) allocations before after ∧
      List.Forall₂ (fun pair allocation => match pair.1.tag with
        | .initial _ => allocation.baseline = 0
        | .fresh _ => True) payments allocations ∧ result.1.slot = s.slot ∧
      FutureEffectiveCover x ⟨fork, result.1⟩ after := by
  -- It follows the pass one queue entry at a time.
  --
  -- A slashed source is dropped, and an unslashed source that cannot withdraw at `next` stops it.
  --
  -- Any other source pays its target.
  --
  -- The tagged pass, its reserved history and every cut are built in the same step.
  induction queue generalizing s result before position with
  | nil =>
    simp only [List.map_nil, passPendingConsolidations, pure, Except.pure,
      Except.ok.injEq] at passed
    subst passed
    exact ⟨[], [], [], [], before, .nil, rfl, .nil reserve, reserve, assignment,
      by simpa using counters, cover, retired, .nil, .nil, rfl, future⟩
  | cons tag tags ih =>
    rw [List.map_cons] at passed
    unfold passPendingConsolidations at passed
    simp only [bind, Except.bind, pure, Except.pure] at passed
    split at passed
    · cases passed
    rename_i v looked
    have found := liftAccessor_ok.mp looked
    have read := getValidator_eq_ok_iff.mp found
    split at passed
    -- A slashed source is dropped.
    · rename_i slashed
      split at passed
      · cases passed
      rename_i recur
      cases passed
      obtain ⟨suffix, consumed, payments, allocations, after, tagged, read', history, cut, assigned,
          counted, covered, activated, owned, baselines, finalSlot, finalFuture⟩ :=
        ih recur (reserveCut_drop_head reserve) (assignmentCut_drop_head assignment) counters
          nextOk exits activationOrder delay caps (List.nodup_cons.mp unique).2
          (fun tag member => apart tag (List.mem_cons_of_mem _ member))
          (fun tag member => initialZero tag (List.mem_cons_of_mem _ member)) cover future retired
          (fun tag member => sources tag (List.mem_cons_of_mem _ member))
      exact ⟨suffix, tag :: consumed, payments, allocations, after,
        .slashed found slashed tagged, by simp [read'],
        .slashed found slashed reserve assignment history,
        cut, assigned, counted, covered, activated, owned, baselines, finalSlot, finalFuture⟩
    rename_i unslashedBool
    have unslashed : v.slashed = false := by simpa using unslashedBool
    split at passed
    -- An unslashed source that cannot withdraw at `next` stops the pass.
    · rename_i later
      cases passed
      exact ⟨tag :: tags, [], [], [], before, .waiting found unslashed later, rfl,
        .waiting found unslashed later reserve assignment, reserve, assignment,
        by simpa using counters, cover, retired, .nil, .nil, rfl, future⟩
    rename_i ready
    have due : v.withdrawableEpoch ≤ next := UInt64.not_lt.mp ready
    split at passed
    · cases passed
    rename_i b balanceOk
    have balance := liftAccessor_ok.mp balanceOk
    split at passed
    · cases passed
    rename_i d debitedOk
    have debited := liftAccessor_ok.mp debitedOk
    split at passed
    · cases passed
    rename_i u creditedOk
    have credited := liftAccessor_ok.mp creditedOk
    split at passed
    · cases passed
    rename_i recur
    cases passed
    -- Any other source pays its target.
    have different := apart tag List.mem_cons_self
    have apartNat := fun same => different (UInt64.toNat_inj.mp same)
    obtain ⟨allocation, middle, round, baseline, moved⟩ :=
      payment_ownedTransfer_exists (t := u) (sourceRound := rounding tag.entry.sourceIndex.toNat)
        reserve found balance due (caps _ _ read) (counters.release_fresh le_rfl)
    obtain ⟨validators, slot, _, _⟩ := pendingTransfer_balances debited credited apartNat
    have original := moved.original_le
    have gone := pendingTransfer_sourceGone (exits _ (Array.mem_of_getElem? read))
      (delay _ _ read) due finite
    have absent : ¬ ∃ q ∈ tags.map (·.entry), q.sourceIndex = tag.entry.sourceIndex := by
      rintro ⟨q, member, same⟩
      obtain ⟨other, inside, entryEq⟩ := List.mem_map.mp member
      exact (List.nodup_cons.mp unique).1
        (List.mem_map.mpr ⟨other, inside, (congrArg (·.sourceIndex) entryEq).trans same⟩)
    have cut := reserveCut_pendingTransfer found debited credited moved different exits due
      gone absent reserve
    have assigned := assignmentCut_transport assignment original (List.sublist_cons_self _ _)
    have covered := endpointCover_pendingTransfer found debited credited moved different nextOk
      twoSlots exits delay due cover
    have futureCovered := futureCover_pendingTransfer found debited credited moved different nextOk
      twoSlots exits activationOrder delay due future
    obtain ⟨w, lookup, activation⟩ := sources tag List.mem_cons_self
    rw [read] at lookup
    cases lookup
    have activated := RetiredActivated.transfer retired
      (RegistryLifecycle.of_data (congrArg (·.data) validators)) _ read activation moved
    obtain ⟨suffix, consumed, payments, allocations, after, tagged, read', history, finalCut,
        finalAssignment, finalCounters, finalCover, finalRetired, finalOwned, finalBaselines,
        finalSlot, finalFuture⟩ :=
      ih recur cut assigned (counters.transfer moved)
        (by simpa only [getCurrentEpoch, slot] using nextOk)
        (by simpa only [ExitsOrdered, validators] using exits)
        (by simpa only [validators] using activationOrder)
        (by simpa only [validators] using delay) (by simpa only [validators] using caps)
        (List.nodup_cons.mp unique).2
        (fun other member => apart other (List.mem_cons_of_mem _ member))
        (fun other member n initial => Nat.eq_zero_of_le_zero
          ((original _).trans_eq (initialZero other (List.mem_cons_of_mem _ member) n initial)))
        covered futureCovered activated
        (fun other member => by
          simpa only [validators] using sources other (List.mem_cons_of_mem _ member))
    have release : match tag.tag with
        | .initial _ => allocation.baseline = 0
        | .fresh _ => allocation.baseline ≤ tag.amount + allocation.sourceRound ∧
            before.original tag.entry.sourceIndex.toNat ≤ tag.amount + allocation.sourceRound := by
      cases taggedTag : tag.tag with
      | initial n => rw [baseline, initialZero tag List.mem_cons_self n taggedTag, Nat.min_zero]
      | fresh n =>
        have bound := assignment tag List.mem_cons_self n taggedTag
        rw [round]
        exact ⟨(baseline ▸ Nat.min_le_right _ _).trans bound, bound⟩
    refine ⟨suffix, tag :: consumed, _ :: payments, allocation :: allocations, after,
      .paid found unslashed due balance debited credited tagged, by simp [read'],
      .paid found unslashed due balance debited credited reserve assignment round moved release
        history,
      finalCut, finalAssignment, ?_, finalCover, finalRetired, .cons moved finalOwned,
      .cons ?_ finalBaselines, finalSlot.trans slot, finalFuture⟩
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using finalCounters
    · cases taggedTag : tag.tag with
      | initial n => simpa only [taggedTag] using release
      | fresh n => trivial

/-- A pairing of tagged payments with allocations gives each payment its allocation by index.

An initial tag has no baseline. -/
private theorem paired_initial_baselines {tagged : List (TaggedEntry × Payment preset)}
    {allocations : List OwnedRelease}
    (paired : List.Forall₂ (fun pair allocation => match pair.1.tag with
      | .initial _ => allocation.baseline = 0
      | .fresh _ => True) tagged allocations) :
    ∀ j : Fin tagged.length, ∃ a, allocations[j.val]? = some a ∧
      (match tagged[j].1.tag with | .initial _ => a.baseline = 0 | .fresh _ => True) := by
  intro j
  -- The two lists have the same length, so the allocation at `j` exists.
  have inside : j.val < allocations.length := paired.length_eq ▸ j.isLt
  exact ⟨allocations[j.val], List.getElem?_eq_getElem inside, paired.get j.isLt inside⟩
/-- A step that keeps the validators and the balances keeps the reserve cut. -/
private theorem reserveCut_records {x : ForkedBeaconState preset} {high : Nat} {fork : Fork}
    {s t : BeaconState preset fork} {epoch : Epoch} {suffix : List PendingConsolidation}
    {owned : Ownership} (validators : t.validators = s.validators)
    (balances : t.balances = s.balances)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned) :
    ReserveCut x high ⟨fork, t⟩ epoch suffix owned := by
  simpa only [ReserveCut, potential, FundingRelevant, effectiveAt, actualBalanceAt, validators,
    balances] using reserve

/-- The pending consolidations leave exactly the suffix of the tagged pass as the actual queue.

The step's queue is the actual queue without its longest front of certain sources.

These sources are slashed or can withdraw at the next epoch, read in the state before the step.

The tagged pass at that same next epoch leaves the same front off the tagged queue. -/
private theorem processPendingConsolidations_erasure {fork : Fork}
    {s t u : BeaconState preset fork} {electra : .pectra ≤ fork} {next : Epoch}
    {queue suffix consumed : List TaggedEntry} {payments : List (TaggedEntry × Payment preset)}
    (ok : processPendingConsolidations s electra = .ok t)
    (pass : TaggedPass next s queue u suffix consumed payments)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (incoming : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    QueueErasure suffix (pendingQueue ⟨fork, t⟩) := by
  -- The checked next epoch is the step's wrapping sum.
  have sum := Uint64.addChecked_ok_iff.mp nextOk
  have nextEq : next = getCurrentEpoch s + 1 :=
    UInt64.toNat_inj.mp (sum.2.trans (Uint64.toNat_add_of_lt sum.1).symm)
  have drop := pass.suffix_drop.2.2
  unfold QueueErasure at incoming ⊢
  simp only [pendingQueue, electra, ↓reduceDIte] at incoming ⊢
  rw [processPendingConsolidations_queue ok, drop, incoming, nextEq]

/-- A successful step of the pending consolidations over an erased tagged queue is a tagged pass.

Its end state has the step's validators and balances.

Its suffix erases the step's queue. -/
private theorem processPendingConsolidations_reserved {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {next : Epoch} {eventPosition position : Nat}
    {s t : BeaconState preset fork} {electra : .pectra ≤ fork} {queue : List TaggedEntry}
    {before : Ownership}
    (ok : processPendingConsolidations s electra = .ok t)
    -- The tagged queue erases that queue.
    (incoming : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (reserve : ReserveCut x high ⟨fork, s⟩ next (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before)
    (counters : OwnershipBefore eventPosition position before)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (finite : next < FAR_FUTURE_EPOCH)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered s)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (delay : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (caps : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      before.original tag.entry.sourceIndex.toNat = 0)
    (cover : EndpointCoverAll x ⟨fork, s⟩ before)
    (future : FutureEffectiveCover x ⟨fork, s⟩ before)
    (retired : RetiredActivated s before.retired)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ u suffix consumed payments allocations after,
      TaggedPass next s queue u suffix consumed payments ∧
      t.validators = u.validators ∧ t.balances = u.balances ∧
      QueueErasure suffix (pendingQueue ⟨fork, t⟩) ∧
      ReservedPayments x high rounding next position s queue u suffix payments allocations
        before after ∧
      ReserveCut x high ⟨fork, u⟩ next (suffix.map (·.entry)) after ∧
      AssignmentCut rounding suffix after ∧
      OwnershipBefore eventPosition (position + payments.length) after ∧
      EndpointCoverAll x ⟨fork, u⟩ after ∧ RetiredActivated u after.retired ∧
      OwnedPayments position (payments.map Prod.snd) allocations before after ∧
      List.Forall₂ (fun pair allocation => match pair.1.tag with
        | .initial _ => allocation.baseline = 0
        | .fresh _ => True) payments allocations ∧ u.slot = s.slot ∧
      FutureEffectiveCover x ⟨fork, u⟩ after := by
  -- The step runs one pass at the checked next epoch over the actual queue.
  --
  -- So the tagged pass and its reserved history follow that pass.
  obtain ⟨result, passOk, balances, _⟩ := processPendingConsolidations_pass ok
  -- The checked next epoch is the step's wrapping sum, and the tagged queue erases its queue.
  have sum := Uint64.addChecked_ok_iff.mp nextOk
  have nextEq : next = getCurrentEpoch s + 1 :=
    UInt64.toNat_inj.mp (sum.2.trans (Uint64.toNat_add_of_lt sum.1).symm)
  have actual : queue.map (·.entry) = (s.pendingConsolidations electra).data.toList := by
    simpa only [QueueErasure, pendingQueue, electra, ↓reduceDIte] using incoming
  rw [← nextEq, ← actual] at passOk
  obtain ⟨suffix, consumed, payments, allocations, after, tagged, _, history, cut, assigned,
      counted, covered, activated, owned, baselines, slot, future'⟩ :=
    TaggedPass.reserved_of_pass (eventPosition := eventPosition) passOk reserve assignment
      counters nextOk finite twoSlots exits activationOrder delay caps unique apart initialZero
      cover future retired sources
  have validators : t.validators = result.1.validators :=
    (processPendingConsolidations_kept ok).1.trans (passPendingConsolidations_kept passOk).1.symm
  exact ⟨result.1, suffix, consumed, payments, allocations, after, tagged, validators, balances,
    processPendingConsolidations_erasure ok tagged nextOk incoming, history, cut, assigned,
    counted, covered, activated, owned, baselines, slot, future'⟩

private theorem tagEvent_consolidations {fork : Fork} {s t u : BeaconState preset fork}
    {queue suffix consumed : List TaggedEntry} {payments : List (TaggedEntry × Payment preset)}
    (electra : .pectra ≤ fork) (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (ok : processPendingConsolidations s electra = .ok t)
    (pass : TaggedPass next s queue u suffix consumed payments)
    (validators : t.validators = u.validators) (balances : t.balances = u.balances)
    (incoming : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    TagEvent (config := config) ⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩
      position queue suffix consumed payments [] :=
  ⟨incoming, processPendingConsolidations_erasure ok pass nextOk incoming,
    Or.inr (Or.inr ⟨fork, s, t, u, electra, next, rfl, rfl, rfl,
    nextOk, ok, pass, validators, balances, rfl⟩)⟩

/-- The pending consolidations over an erased tagged queue are a reserved consolidation event.

The single pass construction gives several results for the same witnesses.

They are the actual tagged pass, its end state with the step's records, and the outgoing erasure.

They also include the event's ownership, cuts and covers. -/
private theorem reservedEvent_consolidations {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {next : Epoch} {eventPosition position : Nat}
    {s t : BeaconState preset fork} {queue : List TaggedEntry} {before : Ownership}
    (electra : .pectra ≤ fork)
    (ok : processPendingConsolidations s electra = .ok t)
    (incoming : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (reserve : ReserveCut x high ⟨fork, s⟩ next (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before)
    (counters : OwnershipBefore eventPosition position before)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered s)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (delay : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (caps : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      before.original tag.entry.sourceIndex.toNat = 0)
    (cover : EndpointCoverAll x ⟨fork, s⟩ before)
    (future : FutureEffectiveCover x ⟨fork, s⟩ before)
    (retired : RetiredActivated s before.retired)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ u suffix consumed payments allocations after,
      TaggedPass next s queue u suffix consumed payments ∧
      t.validators = u.validators ∧ t.balances = u.balances ∧
      QueueErasure suffix (pendingQueue ⟨fork, t⟩) ∧
      ReservedEvent x high eventPosition position rounding
        ⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ queue suffix payments allocations before after
            ∧
      OwnershipBefore eventPosition (position + payments.length) after ∧
      ReserveCut x high ⟨fork, t⟩ next (suffix.map (·.entry)) after ∧
      EndpointCoverAll x ⟨fork, t⟩ after ∧ RetiredActivated t after.retired ∧
      FutureEffectiveCover x ⟨fork, t⟩ after := by
  obtain ⟨u, suffix, consumed, payments, allocations, after, pass, validators, balances,
      outgoing, history, cut, assigned, counted, covered, activated, owned, baselines, slot,
      finalFuture⟩ :=
    processPendingConsolidations_reserved (eventPosition := eventPosition) ok incoming reserve
      assignment counters nextOk (nextEpoch_lt_farFuture twoSlots nextOk) twoSlots exits
      activationOrder delay caps unique apart initialZero cover future retired sources
  have slotEq : t.slot = u.slot := (frame_processPendingConsolidations ok).slot.trans slot.symm
  have retiredT : RetiredActivated t after.retired := by
    simpa only [RetiredActivated, validators] using activated
  refine ⟨u, suffix, consumed, payments, allocations, after, pass, validators, balances,
    outgoing, ?_, counted, reserveCut_records validators balances cut,
    endpointCoverAll_records validators balances slotEq covered, retiredT,
    futureCover_records validators (by
      simp only [getCurrentEpoch, slotEq]
      exact UInt64.le_refl _) finalFuture⟩
  refine ⟨?_, assignment, assigned, ?_⟩
  · simp only [OwnedEvent, ↓reduceIte]
    exact ⟨owned, paired_initial_baselines baselines⟩
  · simp only [↓reduceIte]
    exact ⟨fork, s, t, u, electra, next, rfl, rfl, nextOk, ok, validators, balances, history⟩

/-- A consolidation event's reserved accounting does not depend on its credit and debit limits. -/
private theorem reservedEvent_consolidations_payload {x : ForkedBeaconState preset}
    {high eventPosition paymentPosition : Nat} {rounding : Nat → Nat}
    {before after : ForkedBeaconState preset} {credit debit credit' debit' : Nat}
    {queue suffix : List TaggedEntry} {tagged : List (TaggedEntry × Payment preset)}
    {allocations : List OwnedRelease} {owned owned' : Ownership} :
    ReservedEvent x high eventPosition paymentPosition rounding
        ⟨.consolidations, before, after, credit, debit⟩ queue suffix tagged allocations
        owned owned' ↔
      ReservedEvent x high eventPosition paymentPosition rounding
        ⟨.consolidations, before, after, credit', debit'⟩ queue suffix tagged allocations
        owned owned' := by
  -- The epoch replay records the pending consolidations.
  --
  -- It sets both limits to the balance the pass consumes.
  --
  -- That is the effective balance of the consumed unslashed sources.
  --
  -- The reserved readers state the same event with limits `0` and `0`.
  --
  -- Neither limit is read on the reserved side.
  --
  -- For a consolidation event, consider its ownership step and the reserve clause of the event.
  --
  -- They read only the source, the two states and the actual tagged pass with its payments.
  --
  -- The moved balance is accounted there, payment by payment.
  --
  -- The funding credit of a consolidation is `0` whatever its limits.
  --
  -- So the two payloads give the same proposition.
  simp only [ReservedEvent, OwnedEvent, ↓reduceIte]

/-- The tag of a consolidation event reads only its source and its two states. -/
private theorem tagEvent_consolidations_payload {before after : ForkedBeaconState preset}
    {credit debit credit' debit' position : Nat} {queue suffix consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)} :
    TagEvent (config := config) ⟨.consolidations, before, after, credit, debit⟩
        position queue suffix consumed payments calls ↔
      TagEvent (config := config) ⟨.consolidations, before, after, credit', debit'⟩
        position queue suffix consumed payments calls :=
  Iff.rfl

/-- The pending consolidations as the head of a reserved replay, with any recorded limits. -/
private theorem reservedReplay_consolidations_cons_payload {fork : Fork}
    {s t u : BeaconState preset fork} {queue middle consumed : List TaggedEntry}
    {tagged : List (TaggedEntry × Payment preset)} {credit debit : Nat}
    (electra : .pectra ≤ fork) (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (ok : processPendingConsolidations s electra = .ok t)
    (pass : TaggedPass next s queue u middle consumed tagged)
    (validators : t.validators = u.validators) (balances : t.balances = u.balances)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, s⟩ startEpoch (getCurrentEpoch s) queue before eventOwned)
    -- The reserved event is the one the readers construct, with limits `0` and `0`.
    (event : ReservedEvent x high eventPosition paymentPosition rounding
      ⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ queue middle tagged allocations
      eventOwned midOwned)
    (rest : ReservedReplay (config := config) (checks := checks) x high rounding
      ⟨fork, t⟩ next finish finishEpoch (eventPosition + 1) (paymentPosition + tagged.length)
      callPosition events middle final payments restAllocations restCalls midOwned after) :
    ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      (⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ :: events) queue final
      (tagged ++ payments) (allocations ++ restAllocations) restCalls before after := by
  -- The replay records the event with the limits the caller needs.
  --
  -- An example is the consumed balance that the epoch replay records.
  --
  -- It does so through the payload bridges above.
  have incoming := frame.2.2.2.2.2.2.1
  have tags :=
      tagEvent_consolidations (config := config) (position := callPosition) electra nextOk ok pass
    validators balances incoming
  have nextEq : getCurrentEpoch s + 1 = next := by
    have checked := Uint64.addChecked_ok_iff.mp nextOk
    apply UInt64.toNat_inj.mp
    exact (Uint64.toNat_add_of_lt checked.1).trans checked.2.symm
  have demand : eventDemandEpoch
      (⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ : BalanceEvent preset) = next := by
    simpa only [eventDemandEpoch, ↓reduceIte] using nextEq
  have replay := ReservedReplay.cons frame (tagEvent_consolidations_payload.mp tags)
    (reservedEvent_consolidations_payload.mp event) (demand ▸ rest)
  simpa only [List.length_nil, Nat.add_zero, List.nil_append] using replay

private theorem nonreference_before_unset_exit {x u : ForkedBeaconState preset} {i : Nat}
    {v : Validator} (life : RegistryLifecycle x.state u.state)
    (flags : SlashedPersistence x.state u.state)
    (found : u.state.validators.data[i]? = some v)
    (unset : v.exitEpoch = FAR_FUTURE_EPOCH) (clean : v.slashed = false)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (notReference : ¬ NewReference x i) :
    (x.state.validators.data[i]?).all (fun initial =>
      !isActiveValidator initial (getCurrentEpoch x.state) &&
        !isActiveValidator initial (getPreviousEpoch x.state)) = true := by
  cases old : x.state.validators.data[i]? with
  | none => simp
  | some initial =>
    obtain ⟨later, read, epochs⟩ := life.validators i initial old
    have same := Option.some.inj (read.symm.trans found)
    subst later
    have exit : initial.exitEpoch = FAR_FUTURE_EPOCH := by
      by_contra assigned
      exact assigned ((epochs.exitEpoch assigned).symm.trans unset)
    have unslashed : initial.slashed = false := by
      by_contra marked
      obtain ⟨later, read, markedLater⟩ := flags i initial old (Bool.eq_true_of_not_eq_false marked)
      have same := Option.some.inj (read.symm.trans found)
      subst later
      simp [clean] at markedLater
    have inactive : isActiveValidator initial (getCurrentEpoch x.state) = false := by
      by_contra active
      apply notReference
      simp [NewReference, old, unslashed, exit, Bool.eq_true_of_not_eq_false active]
    have previous : isActiveValidator initial (getPreviousEpoch x.state) = false := by
      by_contra active
      have active := Bool.eq_true_of_not_eq_false active
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
      have bound := UInt64.le_trans active.1 (getPreviousEpoch_le x.state)
      have below : getCurrentEpoch x.state < initial.exitEpoch := exit ▸ finite
      have now : isActiveValidator initial (getCurrentEpoch x.state) = true := by
        simp [isActiveValidator, bound, below]
      simp [inactive] at now
    simp [inactive, previous]

/-- Valid ownership, left unchanged, is an owned frame. -/
theorem OwnedFrame.refl {owned : Ownership} (valid : OwnershipValid owned) :
    OwnedFrame owned owned :=
  ⟨valid, valid, rfl, fun _ => Or.inl rfl, Finset.Subset.refl _, rfl, fun _ => Nat.le_refl _⟩

/-- Take a silent epoch stage that keeps the validators, the balances and the queue.

It is a reserved frame. -/
private theorem reservedFrame_records_stage {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {s t : BeaconState preset fork} {epoch : Epoch}
    {queue : List TaggedEntry} {owned : Ownership} {stage : EpochStage}
    (silent : SilentStage stage) (ok : EpochStage.action config checks stage s = .ok t)
    (other : stage ≠ .rewards ∧ stage ≠ .registry ∧ stage ≠ .slashings ∧
      stage ≠ .pendingDeposits ∧ stage ≠ .pendingConsolidations ∧ stage ≠ .effectiveBalances)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned := by
  obtain ⟨validators, balances, sameQueue, _, _⟩ := (EpochStage.action_cases.mp ok).records other
  have queueEq : pendingQueue ⟨fork, t⟩ = pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, sameQueue]
  exact ⟨.cons (.epoch silent ok) .nil, UInt64.le_refl _, OwnedFrame.refl reserve.1, assignment,
    assignment, erasure, queueEq ▸ erasure, reserve, reserveCut_records validators balances reserve⟩

/-- Let each supported validator's capped balance be covered at the endpoint.

Then the effective-balance update keeps the reserve cut. -/
private theorem reserveCut_effective {x : ForkedBeaconState preset} {high : Nat} {fork : Fork}
    {s t : BeaconState preset fork} {epoch : Epoch} {suffix : List PendingConsolidation}
    {owned : Ownership} (ok : processEffectiveBalanceUpdates s = .ok t)
    -- The endpoint clause bounds only the effective balance, so this hypothesis covers a raise.
    (endpointBalance : ∀ i v, s.validators.data[i]? = some v → SupportedAt epoch v →
      v.pubkey ∉ previousOnly x →
      min (actualBalanceAt ⟨fork, s⟩ i) (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
          (held owned i ∩ owned.endpoint).card)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned) :
    ReserveCut x high ⟨fork, t⟩ epoch suffix owned := by
  -- The update keeps each effective balance or sets it to at most the capped balance.
  --
  -- Every clause but the endpoint one already bounds the capped balance.
  have balancesEq := processEffectiveBalanceUpdates_balances ok
  have capS : ∀ v,
      withdrawalMaxEffectiveBalance preset (⟨fork, s⟩ : ForkedBeaconState preset).fork v =
        withdrawalMaxEffectiveBalance preset fork v := fun _ => rfl
  have balance : ∀ i, actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) i =
      actualBalanceAt ⟨fork, s⟩ i := by
    intro i
    simp only [actualBalanceAt, balancesEq]
  -- Each validator after the update is the one before with a new effective balance.
  --
  -- That balance is the old one or at most the capped balance.
  have lookup : ∀ i w, t.validators.data[i]? = some w → ∃ v e,
      s.validators.data[i]? = some v ∧ w = { v with effectiveBalance := e } ∧
      (e.toNat = v.effectiveBalance.toNat ∨
        e.toNat ≤ min (actualBalanceAt ⟨fork, s⟩ i)
          (withdrawalMaxEffectiveBalance preset fork v).toNat) := by
    intro i w found
    have inside : i < s.validators.data.size :=
      (sameSizes_processEffectiveBalanceUpdates ok).1 ▸ (Array.getElem?_eq_some_iff.mp found).1
    obtain ⟨v, amount, foundS, owned⟩ := effective_update_input_reads ok inside
    obtain ⟨e, read, bound⟩ := processEffectiveBalanceUpdates_effectiveBalance ok foundS owned
    rw [read] at found
    cases found
    refine ⟨v, e, foundS, rfl, ?_⟩
    have amountAt : actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i = amount.toNat := by
      simp [actualBalanceAt, owned]
    rcases bound with same | ⟨below, capped⟩
    · exact Or.inl (by rw [same])
    · right
      rw [amountAt]
      exact Nat.le_min.mpr ⟨UInt64.le_iff_toNat_le.mp below, UInt64.le_iff_toNat_le.mp capped⟩
  have effectiveT : ∀ i (v : Validator) (e : Gwei),
      t.validators.data[i]? = some { v with effectiveBalance := e } →
      effectiveAt (⟨fork, t⟩ : ForkedBeaconState preset) i = e.toNat := by
    intro i v e found
    simp [effectiveAt, found]
  have effectiveS : ∀ i (v : Validator), s.validators.data[i]? = some v →
      effectiveAt (⟨fork, s⟩ : ForkedBeaconState preset) i = v.effectiveBalance.toNat := by
    intro i v found
    simp [effectiveAt, found]
  have relevant : ∀ i, FundingRelevant ⟨fork, t⟩ epoch suffix i →
      FundingRelevant ⟨fork, s⟩ epoch suffix i := by
    rintro i ⟨w, found, rest⟩
    obtain ⟨v, e, foundS, rfl, _⟩ := lookup i w found
    exact ⟨v, foundS, rest⟩
  obtain ⟨valid, wasRetired, wasOriginal, reference, scheduled, pending, due, idle,
    activePending, endpoint⟩ := reserve
  refine ⟨valid, ?_, wasOriginal, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member w found
    obtain ⟨v, e, foundS, rfl, _⟩ := lookup i w found
    exact wasRetired i member v foundS
  · intro i ref notRetired support
    have old := reference i ref notRetired (relevant i support)
    obtain ⟨w, found, _⟩ := support
    obtain ⟨v, e, foundS, rfl, bound⟩ := lookup i w found
    have cap : withdrawalMaxEffectiveBalance preset fork { v with effectiveBalance := e } =
        withdrawalMaxEffectiveBalance preset fork v := rfl
    simp only [potential, found, foundS, Option.map_some, Option.getD_some] at old ⊢
    rw [cap, balance]
    omega
  · intro i initial w found active clean finite located support
    obtain ⟨v, e, foundS, rfl, bound⟩ := lookup i w located
    have old := scheduled i initial v found active clean finite foundS support
    rw [effectiveT i v e located, balance]
    rw [effectiveS i v foundS, capS] at old
    exact max_le (by omega) (le_of_max_le_right old)
  · intro i initial notRetired support w found
    obtain ⟨v, e, foundS, rfl, _⟩ := lookup i w found
    have old := pending i initial notRetired (relevant i support) v foundS
    rw [balance]
    exact old
  · intro entry member w found ready notRef
    obtain ⟨v, e, foundS, rfl, _⟩ := lookup _ w found
    have old := due entry member v foundS ready notRef
    rw [balance]
    exact old
  · intro i w found notRef notPending quiet support
    obtain ⟨v, e, foundS, rfl, bound⟩ := lookup i w found
    have old := idle i v foundS notRef notPending quiet support
    rw [effectiveT i v e found, balance]
    rw [effectiveS i v foundS, capS] at old
    exact max_le (by omega) (le_of_max_le_right old)
  · intro i initial w old located found active notRetired support
    obtain ⟨v, e, foundS, rfl, bound⟩ := lookup i w located
    obtain ⟨capped, effective⟩ := activePending i initial v old foundS found active notRetired
      (relevant i support)
    rw [effectiveT i v e located, balance]
    rw [effectiveS i v foundS] at effective
    rw [capS] at capped
    exact ⟨capped, by omega⟩
  · intro i w found support notPrevious
    obtain ⟨v, e, foundS, rfl, bound⟩ := lookup i w found
    have old := endpoint i v foundS support notPrevious
    have raised := endpointBalance i v foundS support notPrevious
    rw [effectiveT i v e found]
    rw [effectiveS i v foundS] at old
    show e.toNat ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
      (held owned i ∩ owned.endpoint).card
    omega

/-- A step that keeps the validators and the balances keeps the endpoint balance cover. -/
private theorem endpointCover_records {x : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {epoch : Epoch} {owned : Ownership}
    (validators : t.validators = s.validators) (balances : t.balances = s.balances)
    (cover : ∀ i v, s.validators.data[i]? = some v → SupportedAt epoch v →
      v.pubkey ∉ previousOnly x →
      min (actualBalanceAt ⟨fork, s⟩ i) (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
          (held owned i ∩ owned.endpoint).card) :
    ∀ i v, t.validators.data[i]? = some v → SupportedAt epoch v →
      v.pubkey ∉ previousOnly x →
      min (actualBalanceAt ⟨fork, t⟩ i) (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
          (held owned i ∩ owned.endpoint).card := by
  intro i v found
  rw [validators] at found
  simpa only [actualBalanceAt, balances] using cover i v found

/-- The effective-balance stage is a reserved frame under the endpoint balance cover. -/
private theorem reservedFrame_effective {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {s t : BeaconState preset fork} {epoch : Epoch}
    {queue : List TaggedEntry} {owned : Ownership}
    (ok : EpochStage.action config checks .effectiveBalances s = .ok t)
    (endpointBalance : ∀ i v, s.validators.data[i]? = some v → SupportedAt epoch v →
      v.pubkey ∉ previousOnly x →
      min (actualBalanceAt ⟨fork, s⟩ i) (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
          (held owned i ∩ owned.endpoint).card)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned := by
  have edge := EpochStage.action_cases.mp ok
  have sameQueue : SamePendingQueue s t := edge.samePendingQueue nofun
  have queueEq : pendingQueue ⟨fork, t⟩ = pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, show t.pendingConsolidations = s.pendingConsolidations from sameQueue]
  exact ⟨.cons (.epoch .effectiveBalances ok) .nil, UInt64.le_refl _, OwnedFrame.refl reserve.1,
    assignment, assignment, erasure, queueEq ▸ erasure, reserve,
    reserveCut_effective (show processEffectiveBalanceUpdates s = .ok t from edge)
      endpointBalance reserve⟩

/-- A records-only epoch stage keeps the endpoint cover and the future cover.

It does so at the same ownership. -/
private theorem covers_records_stage {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {owned : Ownership} {stage : EpochStage}
    (step : EpochStage.action config checks stage u = .ok v)
    (other : stage ≠ .rewards ∧ stage ≠ .registry ∧ stage ≠ .slashings ∧
      stage ≠ .pendingDeposits ∧ stage ≠ .pendingConsolidations ∧ stage ≠ .effectiveBalances) :
    (EndpointCoverAll x ⟨fork, u⟩ owned → EndpointCoverAll x ⟨fork, v⟩ owned) ∧
      (FutureEffectiveCover x ⟨fork, u⟩ owned → FutureEffectiveCover x ⟨fork, v⟩ owned) := by
  obtain ⟨validators, balances, _, _, slot⟩ := (EpochStage.action_cases.mp step).records other
  exact ⟨endpointCoverAll_records validators balances slot,
    futureCover_records validators (by simp only [getCurrentEpoch, slot]; exact UInt64.le_refl _)⟩

/-- The silent suffix of an epoch after the pending consolidations is a reserved frame.

It keeps the endpoint cover and the future cover at the same ownership. -/
private theorem reservedFrame_epochSuffix_lifecycle {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {s t : BeaconState preset fork} {epoch : Epoch}
    {queue : List TaggedEntry} {owned : Ownership}
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) s t)
    -- That update needs the endpoint balance cover at the start, which the payments stage keeps.
    (endpointBalance : ∀ i v, s.validators.data[i]? = some v → SupportedAt epoch v →
      v.pubkey ∉ previousOnly x →
      min (actualBalanceAt ⟨fork, s⟩ i) (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
          (held owned i ∩ owned.endpoint).card)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, s⟩ ⟨fork, t⟩ epoch epoch queue owned owned ∧
      (BalancesMatch s → EndpointCoverAll x ⟨fork, s⟩ owned → EndpointCoverAll x ⟨fork, t⟩ owned) ∧
      (BalancesMatch s → (∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
        EndpointCoverAll x ⟨fork, s⟩ owned → FutureEffectiveCover x ⟨fork, s⟩ owned →
          FutureEffectiveCover x ⟨fork, t⟩ owned) ∧
      RegistryLifecycle s t := by
  -- Its stages keep the validators, the balances, the queue and the slot.
  --
  -- The exception is the effective-balance update, which moves effective balances only.
  --
  -- The future cover through that update also needs three facts.
  --
  -- The first is matching balances.
  --
  -- The second is activations no later than exits.
  --
  -- The third is the endpoint cover at the input of that update.
  --
  -- The payments stage keeps that endpoint cover from the start.
  simp only [EpochStage.middleStages, EpochStage.tailStages, List.cons_append,
    List.nil_append] at trace
  cases trace with | cons paid trace =>
  cases trace with | cons updated trace =>
  cases trace with | cons slashings trace =>
  cases trace with | cons randao trace =>
  cases trace with | cons history trace =>
  cases trace with | cons participation trace =>
  cases trace with | cons sync trace =>
  cases trace with | cons lookahead trace =>
  cases trace with | cons ptc trace =>
  cases trace
  have one := reservedFrame_records_stage (config := config) (checks := checks) .payments paid
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩ reserve assignment erasure
  -- The payments stage keeps the validators and the balances, so the cover still holds.
  obtain ⟨validators, balances, _, _, _⟩ :=
    (EpochStage.action_cases.mp paid).records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have two := reservedFrame_effective (config := config) (checks := checks) updated
    (endpointCover_records validators balances endpointBalance)
    one.2.2.2.2.2.2.2.2 one.2.2.2.2.1 one.2.2.2.2.2.2.1
  have next := fun {stage : EpochStage} {u v : BeaconState preset fork}
      (silent : SilentStage stage) (step : EpochStage.action config checks stage u = .ok v)
      (frame : ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, s⟩ ⟨fork, u⟩ epoch epoch queue owned owned)
      (other : stage ≠ .rewards ∧ stage ≠ .registry ∧ stage ≠ .slashings ∧
        stage ≠ .pendingDeposits ∧ stage ≠ .pendingConsolidations ∧
        stage ≠ .effectiveBalances) =>
    frame.trans (reservedFrame_records_stage (config := config) (checks := checks) silent step
      other frame.2.2.2.2.2.2.2.2 frame.2.2.2.2.1 frame.2.2.2.2.2.2.1)
  have upTo := one.trans two
  have all := next .ptcWindow ptc (next .proposerLookahead lookahead (next .syncCommittees sync
    (next .participation participation (next .history history (next .randaoReset randao
      (next .slashingsReset slashings upTo ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩)
      ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩)
      ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩)
      ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  -- The same stages carry both covers.
  --
  -- The payments stage and the stages after the update keep the records.
  --
  -- The update keeps both covers from the endpoint cover at its input.
  have c0 := covers_records_stage (x := x) (owned := owned) paid
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c1 := covers_records_stage (x := x) (owned := owned) slashings
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c2 := covers_records_stage (x := x) (owned := owned) randao
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c3 := covers_records_stage (x := x) (owned := owned) history
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c4 := covers_records_stage (x := x) (owned := owned) participation
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c5 := covers_records_stage (x := x) (owned := owned) sync
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c6 := covers_records_stage (x := x) (owned := owned) lookahead
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have c7 := covers_records_stage (x := x) (owned := owned) ptc
    ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have updatedOk := (show processEffectiveBalanceUpdates _ = .ok _ from
    EpochStage.action_cases.mp updated)
  -- The payments stage keeps the registry and the balances, so their sizes still match.
  have matchedPaid : BalancesMatch s → BalancesMatch _ := fun matched => by
    unfold BalancesMatch at matched ⊢
    rw [validators, balances]
    exact matched
  -- Every suffix stage keeps the registry lifecycle.
  have life : RegistryLifecycle s t :=
    ((((((((EpochStage.action_cases.mp paid).registryLifecycle.trans
      (EpochStage.action_cases.mp updated).registryLifecycle).trans
      (EpochStage.action_cases.mp slashings).registryLifecycle).trans
      (EpochStage.action_cases.mp randao).registryLifecycle).trans
      (EpochStage.action_cases.mp history).registryLifecycle).trans
      (EpochStage.action_cases.mp participation).registryLifecycle).trans
      (EpochStage.action_cases.mp sync).registryLifecycle).trans
      (EpochStage.action_cases.mp lookahead).registryLifecycle).trans
      (EpochStage.action_cases.mp ptc).registryLifecycle
  refine ⟨all, fun matched endpoint => ?_, fun matched activation endpoint future => ?_, life⟩
  · exact c7.1 (c6.1 (c5.1 (c4.1 (c3.1 (c2.1 (c1.1
      (endpointCover_effective updatedOk (matchedPaid matched) (c0.1 endpoint))))))))
  · exact c7.2 (c6.2 (c5.2 (c4.2 (c3.2 (c2.2 (c1.2
      (futureCover_effective updatedOk (matchedPaid matched)
        (fun v member => activation v (by rw [← validators]; exact member)) (c0.1 endpoint)
        (c0.2 future))))))))

/-- Support at the epoch after `c` puts the exit after `c`.

The validator is active at that epoch or at `c` itself, with no wrap. -/
private theorem supportedAt_next_exit {v : Validator} {c n : Epoch}
    (step : n.toNat = c.toNat + 1) (supported : SupportedAt n v) : c < v.exitEpoch := by
  rcases supported.2 with now | before
  · simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
      at now
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  · have previous : n - 1 = c := UInt64.toNat_inj.mp (by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp only [UInt64.reduceToNat]
      omega)
    rw [previous] at before
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at before
    exact before.2

/-- The pending consolidations, then the silent suffix of the epoch, at the same event ownership. -/
private theorem reservedEvent_consolidations_suffix_retired {x : ForkedBeaconState preset}
    {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {next : Epoch} {eventPosition position : Nat}
    {s t z : BeaconState preset fork} {queue : List TaggedEntry} {before : Ownership}
    (electra : .pectra ≤ fork)
    (ok : processPendingConsolidations s electra = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ next (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before)
    (counters : OwnershipBefore eventPosition position before)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered s)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (delay : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (caps : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      before.original tag.entry.sourceIndex.toNat = 0)
    (cover : EndpointCoverAll x ⟨fork, s⟩ before)
    (future : FutureEffectiveCover x ⟨fork, s⟩ before)
    (retired : RetiredActivated s before.retired)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (matched : BalancesMatch s)
    (start : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    (incoming : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) t z) :
    ∃ u suffix consumed payments allocations after,
      TaggedPass next s queue u suffix consumed payments ∧
      t.validators = u.validators ∧ t.balances = u.balances ∧
      ReservedEvent x high eventPosition position rounding
        ⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ queue suffix payments allocations before after
            ∧
      OwnershipBefore eventPosition (position + payments.length) after ∧
      RetiredActivated t after.retired ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, z⟩ next next suffix after after ∧
      EndpointCoverAll x ⟨fork, z⟩ after ∧ FutureEffectiveCover x ⟨fork, z⟩ after ∧
      RetiredActivated z after.retired := by
  -- The consolidation event gives its ownership `after` and the reserve cut at `next`.
  --
  -- It also gives the endpoint cover and the future cover at the actual result `t`.
  --
  -- The pending consolidations keep the registry and the matching sizes.
  --
  -- So the balance match and the activation order move from `s` to `t`.
  --
  -- At `t` the endpoint cover gives the suffix's endpoint balance premise at `next`.
  --
  -- A validator supported at `next` exits after the current epoch.
  --
  -- That epoch is at least the start epoch.
  --
  -- The suffix then keeps the frame and both covers at `after`.
  obtain ⟨u, suffix, consumed, payments, allocations, after, pass, validators, balances, outgoing,
      event, counted, cut, covered, retiredT, futureT⟩ :=
    reservedEvent_consolidations (eventPosition := eventPosition) (position := position) electra ok
      incoming reserve
      assignment counters nextOk twoSlots exits activationOrder delay caps unique apart
      initialZero cover future retired sources
  -- The pending consolidations keep the registry, the matching sizes and the slot.
  have kept := (processPendingConsolidations_kept ok).1
  have edge : EpochStage.Edge config checks .pendingConsolidations s t := by
    simp only [EpochStage.Edge, electra, ↓reduceDIte]
    exact ok
  have matchedT := EpochStage.Edge.balancesMatch_of_not_justification edge nofun matched
  have activationT : ∀ v ∈ t.validators.data, v.activationEpoch ≤ v.exitEpoch := by
    rw [kept]
    exact activationOrder
  have epochT : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, (frame_processPendingConsolidations ok).slot]
  have step : next.toNat = (getCurrentEpoch t).toNat + 1 := by
    rw [epochT]
    simpa only [UInt64.reduceToNat] using (Uint64.addChecked_ok_iff.mp nextOk).2
  -- A validator supported at `next` exits after the current epoch, hence after the start epoch.
  have endpointBalance : ∀ i v, t.validators.data[i]? = some v → SupportedAt next v →
      v.pubkey ∉ previousOnly x →
      min (actualBalanceAt ⟨fork, t⟩ i) (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
          (held after i ∩ after.endpoint).card := by
    intro i v found supported _
    have exits := supportedAt_next_exit step supported
    exact covered i v found supported.1
      (UInt64.lt_of_le_of_lt (epochT ▸ start) exits) (UInt64.le_of_lt exits)
  obtain ⟨frame, endpointT, futureW, life⟩ := reservedFrame_epochSuffix_lifecycle
    (config := config) (checks := checks) (rounding := rounding) trace endpointBalance cut
      event.2.2.1 outgoing
  exact ⟨u, suffix, consumed, payments, allocations, after, pass, validators, balances, event,
    counted, retiredT, frame, endpointT matchedT covered,
    futureW matchedT activationT covered futureT, retiredT.lifecycle life⟩

/-- The epoch prefix up to the pending consolidations, as one reserved replay.

```text
    s --justification, inactivity--> scored --rewards--> rewarded
      -- registry--> registered --slashings--> slashed --eth1 reset--> reset pending deposits--> t
```

These are the stages before the payments, in the order of the epoch schedule. -/
private theorem reservedReplay_epochPrefixDeposits_owned {fork : Fork}
    {s reset t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (epoch : ReplayedPrefix config checks s reset)
    (deposits : processPendingDeposits config checks reset electra = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (retired : RetiredActivated s owned.retired)
    (startLife : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delayed : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat)
    (delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∃ after, ReservedReplay (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, t⟩ (getCurrentEpoch t)
      eventPosition paymentPosition callPosition
      (epoch.recorded ++
        [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩,
        ⟨.deposits, ⟨fork, reset⟩, ⟨fork, t⟩, consumedDeposits reset t electra, 0⟩])
      queue queue [] [] [] owned after ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue after after ∧
      QueueErasure queue (pendingQueue ⟨fork, t⟩) ∧
      OwnershipBefore (eventPosition + (epoch.recorded.length + 2)) paymentPosition after ∧
      BalancesMatch t ∧ RetiredActivated t after.retired ∧
      (EndpointCoverAll x ⟨fork, s⟩ owned → EndpointCoverAll x ⟨fork, t⟩ after) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ owned → FutureEffectiveCover x ⟨fork, t⟩ after) ∧
      t.slot = s.slot ∧ RegistryLifecycle s t ∧ ExitsOrdered t ∧
      (∀ (i : Nat) (v : Validator), t.validators.data[i]? = some v →
        v.exitEpoch ≠ FAR_FUTURE_EPOCH →
          v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            v.withdrawableEpoch.toNat) ∧
      ((∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
        ∀ v ∈ t.validators.data, v.activationEpoch ≤ v.exitEpoch) ∧
      after.original = owned.original := by
  -- Each step hands its own output frame to the next.
  --
  -- The eth1 reset keeps the registry, the balances and the queue.
  --
  -- So it carries the slashings frame and both covers with the same ownership.
  --
  -- The queue erasure at `t` is the one the pending-deposit event establishes.
  --
  -- The facts the stages need in between come from the epoch start.
  --
  -- The epoch prefix carries the slot, the queue order, the exits and the delay to `reset`.
  --
  -- Each stage keeps the registry lifecycle.
  --
  -- `2 <= MIN_VALIDATOR_WITHDRAWABILITY_DELAY` gives the two epochs the deposit step reads.
  have rewardsEdge : EpochStage.Edge config checks .rewards epoch.scored epoch.rewarded :=
    epoch.rewardedOk
  have registryEdge : EpochStage.Edge config checks .registry epoch.rewarded epoch.registered :=
    epoch.registeredOk
  have slashingsEdge : EpochStage.Edge config checks .slashings epoch.registered epoch.slashed :=
    epoch.slashedOk
  -- The actual stage trace from the epoch start to the deposit input.
  have trace := epoch.trace
  obtain ⟨resetSlot, resetOrdered, resetExits, resetDelayed⟩ :=
    deposit_prefix_facts trace ordered exits delayed
  obtain ⟨rewardedOwned, rewards, rewardedFrame, rewardedCounters, rewardedMatched,
      rewardedCover, rewardedFuture, retiredSame, registrySame, originalSame⟩ :=
    reservedReplay_epochRewardStart_owned (callPosition := callPosition) electra matched
      epoch.justifiedOk epoch.scoredOk epoch.replay reserve assignment erasure prior
  -- Rewards keep the registry and the retired set, so retired sources stay activated.
  have rewardedRetired : RetiredActivated epoch.rewarded rewardedOwned.retired := by
    intro i member
    rw [retiredSame] at member
    obtain ⟨v, found, assigned⟩ := retired i member
    exact ⟨v, by rw [registrySame]; exact found, assigned⟩
  have rewardedLife : RegistryLifecycle s epoch.rewarded := RegistryLifecycle.of_data registrySame
  have rewardedExits : ExitsOrdered epoch.rewarded := by
    simpa only [ExitsOrdered, registrySame] using exits
  have rewardedEpoch : getCurrentEpoch epoch.rewarded = getCurrentEpoch s := by
    simp only [getCurrentEpoch, rewardsEdge.slot_eq, epoch.scoredOk.slot_eq,
      epoch.justifiedOk.slot_eq]
  obtain ⟨middle, slashedFrame, slashedCover, slashedFuture⟩ :=
    reservedReplay_registrySlashings_frame (callPosition := callPosition) electra early
      rewardedMatched epoch.registeredOk epoch.slashedOk epoch.limitOk rewardedRetired
      (startLife.trans rewardedLife)
      startFinite rewardedExits (rewardedEpoch ▸ finite) rewardedFrame rewardedCounters
  have slashedCounters := middle.counters rewardedCounters
  simp only [List.length_singleton, List.length_nil, Nat.add_zero] at slashedCounters
  have registeredMatched : BalancesMatch epoch.registered :=
    registryEdge.balancesMatch_of_not_justification (by simp) rewardedMatched
  have slashedMatched : BalancesMatch epoch.slashed :=
    balancesMatch_of_sameSizes (sameSizes_processSlashings epoch.slashedOk) registeredMatched
  -- The eth1 reset keeps the registry, the balances, the queue and the slot.
  obtain ⟨resetValidators, resetBalances, _⟩ := epoch.resetOk.records (by simp)
  have resetEpoch : getCurrentEpoch reset = getCurrentEpoch epoch.slashed := by
    simp only [getCurrentEpoch, epoch.resetOk.slot_eq]
  have resetFrame : ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, epoch.slashed⟩ ⟨fork, reset⟩ (getCurrentEpoch epoch.slashed) (getCurrentEpoch reset)
      queue
      (creditOwnership (eventPosition + epoch.recorded.length)
        ⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩
        rewardedOwned)
      (creditOwnership (eventPosition + epoch.recorded.length)
        ⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩
        rewardedOwned) := by
    rw [resetEpoch]
    exact reservedFrame_records_stage .eth1Reset (EpochStage.action_cases.mpr epoch.resetOk)
      (by simp) slashedFrame.2.2.2.2.2.2.2.2 slashedFrame.2.2.2.2.1 slashedFrame.2.2.2.2.2.2.1
  have resetMatched : BalancesMatch reset :=
    epoch.resetOk.balancesMatch_of_not_justification (by simp) slashedMatched
  have resetLife : RegistryLifecycle s reset :=
    ((rewardedLife.trans (registryLifecycle_processRegistryUpdates epoch.registeredOk)).trans
      slashingsEdge.registryLifecycle).trans epoch.resetOk.registryLifecycle
  have resetFinite : getCurrentEpoch reset < FAR_FUTURE_EPOCH := by
    simpa only [getCurrentEpoch, resetSlot] using finite
  -- The configured delay is at least the two epochs the deposit step reads.
  have resetDelay : ∀ (i : Nat) (v : Validator), reset.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat := by
    intro i v found assigned
    have := resetDelayed i v found assigned
    omega
  obtain ⟨last, finalFrame, finalCover, finalFuture⟩ :=
    reservedReplay_processPendingDeposits_frame (callPosition := callPosition) electra
      resetMatched resetOrdered resetExits resetFinite resetDelay
      ((startLife.trans resetLife).size_le) deposits resetFrame slashedCounters
  have finalCounters := last.counters slashedCounters
  simp only [List.length_singleton, List.length_nil, Nat.add_zero] at finalCounters
  -- The three replays join at the frames each step produced.
  have tail := middle.append
    (by simpa only [List.length_singleton, List.length_nil, Nat.add_zero] using last)
  have joined := rewards.append
    (by simpa only [List.length_nil, Nat.add_zero] using tail)
  have depositEdge : EpochStage.Edge config checks .pendingDeposits reset t := by
    simp only [EpochStage.Edge, electra, ↓reduceDIte]
    exact deposits
  refine ⟨_, by simpa only [List.singleton_append, List.nil_append] using joined, finalFrame,
    finalFrame.2.2.2.2.2.2.1, by simpa only [Nat.add_assoc] using finalCounters,
    depositEdge.balancesMatch_of_not_justification (by simp) resetMatched,
    (rewardedRetired.lifecycle
      ((((registryLifecycle_processRegistryUpdates epoch.registeredOk).trans
        slashingsEdge.registryLifecycle).trans epoch.resetOk.registryLifecycle).trans
          depositEdge.registryLifecycle)),
    fun initial => finalCover ?_, fun initial => finalFuture ?_,
    depositEdge.slot_eq.trans resetSlot, resetLife.trans depositEdge.registryLifecycle,
    (frame_processPendingDeposits deposits).toFrame.exitsOrdered resetExits,
    depositEdge.exit_withdrawable_delay resetDelayed, fun order => ?_,
    -- The slashings and deposit credits keep the original balances.
    originalSame⟩
  rotate_left 2
  · -- Every stage of the prefix keeps the activation-exit order.
    exact depositEdge.activationExitOrder <| epoch.resetOk.activationExitOrder <|
      slashingsEdge.activationExitOrder <| registryEdge.activationExitOrder <|
      rewardsEdge.activationExitOrder <| epoch.scoredOk.activationExitOrder <|
      epoch.justifiedOk.activationExitOrder order
  · exact endpointCoverAll_records resetValidators resetBalances epoch.resetOk.slot_eq
      (slashedCover (rewardedCover initial))
  · exact futureCover_records resetValidators (by
      simp only [getCurrentEpoch, epoch.resetOk.slot_eq]
      exact UInt64.le_refl _) (slashedFuture (rewardedFuture initial))

theorem reservedReplay_epochPrefixDeposits_facts {fork : Fork}
    {s reset t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (epoch : ReplayedPrefix config checks s reset)
    (deposits : processPendingDeposits config checks reset electra = .ok t)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (retired : RetiredActivated s owned.retired)
    (startLife : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delayed : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat)
    (delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∃ after, ReservedReplay (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, t⟩ (getCurrentEpoch t)
      eventPosition paymentPosition callPosition
      (epoch.recorded ++
        [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩,
        ⟨.deposits, ⟨fork, reset⟩, ⟨fork, t⟩, consumedDeposits reset t electra, 0⟩])
      queue queue [] [] [] owned after ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue after after ∧
      QueueErasure queue (pendingQueue ⟨fork, t⟩) ∧
      OwnershipBefore (eventPosition + (epoch.recorded.length + 2)) paymentPosition after ∧
      BalancesMatch t ∧ RetiredActivated t after.retired ∧
      (EndpointCoverAll x ⟨fork, s⟩ owned → EndpointCoverAll x ⟨fork, t⟩ after) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ owned → FutureEffectiveCover x ⟨fork, t⟩ after) ∧
      t.slot = s.slot ∧ RegistryLifecycle s t ∧ ExitsOrdered t ∧
      (∀ (i : Nat) (v : Validator), t.validators.data[i]? = some v →
        v.exitEpoch ≠ FAR_FUTURE_EPOCH →
          v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            v.withdrawableEpoch.toNat) ∧
      ((∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch) →
        ∀ v ∈ t.validators.data, v.activationEpoch ≤ v.exitEpoch) := by
  obtain ⟨after, history, frame, erasureT, counters, matchedT, retiredT, cover, future, slotT,
      lifeT, exitsT, delayT, activationT, _⟩ :=
    reservedReplay_epochPrefixDeposits_owned (callPosition := callPosition) electra early matched
      epoch deposits reserve
      assignment erasure prior retired startLife startFinite ordered exits finite delayed delayTwo
  exact ⟨after, history, frame, erasureT, counters, matchedT, retiredT, cover, future, slotT, lifeT,
    exitsT, delayT, activationT⟩

/-- The pending consolidations and the silent suffix of the epoch, as one reserved replay.

```text
    start ==frame==> s --pending consolidations--> t ==silent suffix==> z
``` -/
private theorem reservedReplay_consolidations_suffix {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {next : Epoch}
    {eventPosition position callPosition : Nat} {credit debit : Nat}
    {start : ForkedBeaconState preset} {startEpoch : Epoch}
    {s t z : BeaconState preset fork} {queue : List TaggedEntry} {owned before : Ownership}
    (electra : .pectra ≤ fork)
    (ok : processPendingConsolidations s electra = .ok t)
    -- The frame into `s` supplies the incoming queue erasure and the assignment cut.
    --
    -- So the event reads no separate erasure hypothesis.
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, s⟩ startEpoch (getCurrentEpoch s) queue owned before)
    (reserve : ReserveCut x high ⟨fork, s⟩ next (queue.map (·.entry)) before)
    (counters : OwnershipBefore eventPosition position owned)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered s)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (delay : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (caps : ∀ (i : Nat) (w : Validator), s.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      before.original tag.entry.sourceIndex.toNat = 0)
    (cover : EndpointCoverAll x ⟨fork, s⟩ before)
    (future : FutureEffectiveCover x ⟨fork, s⟩ before)
    (retired : RetiredActivated s before.retired)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (matched : BalancesMatch s)
    (startCurrent : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) t z) :
    ∃ u suffix consumed payments allocations after,
      TaggedPass next s queue u suffix consumed payments ∧
      t.validators = u.validators ∧ t.balances = u.balances ∧
      ReservedReplay (config := config) (checks := checks) x high rounding
        start startEpoch ⟨fork, z⟩ next eventPosition position callPosition
        [⟨.consolidations, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] queue suffix payments
        allocations [] owned after ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, z⟩ next next suffix after after ∧
      OwnershipBefore (eventPosition + 1) (position + payments.length) after ∧
      RetiredActivated z after.retired ∧
      EndpointCoverAll x ⟨fork, z⟩ after ∧ FutureEffectiveCover x ⟨fork, z⟩ after := by
  -- The event is the one pass construction of the pending consolidations with the silent suffix.
  --
  -- The replay records it with the limits the caller needs.
  --
  -- An example is the consumed balance that the epoch replay records.
  --
  -- It ends in the suffix frame at the event's ownership `after`.
  --
  -- The retired sources stay activated at `z`.
  --
  -- That holds since every suffix stage keeps the registry lifecycle.
  --
  -- The reserve cut at `next` stays a premise.
  obtain ⟨u, suffix, consumed, payments, allocations, after, pass, validators, balances, event,
      counted, _, suffixFrame, endpointZ, futureZ, retiredZ⟩ :=
    reservedEvent_consolidations_suffix_retired electra ok reserve frame.2.2.2.2.1
      (counters.frame frame.2.2.1)
      nextOk twoSlots exits activationOrder delay caps unique apart initialZero cover future
      retired sources matched startCurrent frame.2.2.2.2.2.2.1 trace
  -- The event's own suffix frame closes the replay.
  have replay := reservedReplay_consolidations_cons_payload (callPosition := callPosition)
    (credit := credit) (debit := debit) (events := []) electra nextOk ok pass validators balances
    frame event (.nil suffixFrame)
  have countedZ := replay.counters counters
  refine ⟨u, suffix, consumed, payments, allocations, after, pass, validators, balances,
    by simpa only [List.append_nil] using replay, suffixFrame, ?_, retiredZ, endpointZ, futureZ⟩
  simpa only [List.length_singleton, List.length_append, List.length_nil, Nat.add_zero]
    using countedZ

/-- The whole-epoch reserved replay, with the facts the prefix fixes at the consolidation input. -/
private theorem reservedReplay_epoch_facts {fork : Fork}
    {s reset deposited consolidated z : BeaconState preset fork}
    {next : Epoch}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (epoch : ReplayedPrefix config checks s reset)
    (depositsOk : EpochStage.Edge config checks .pendingDeposits reset deposited)
    (consolidationsOk : EpochStage.Edge config checks .pendingConsolidations deposited consolidated)
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) consolidated z)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (retired : RetiredActivated s owned.retired)
    (startCover : EndpointCoverAll x ⟨fork, s⟩ owned)
    (startFuture : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (startLife : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (startCurrent : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delayed : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat)
    (delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (caps : ∀ (i : Nat) (w : Validator), deposited.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ after, ReservedReplay (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, deposited⟩ (getCurrentEpoch deposited)
      eventPosition paymentPosition callPosition
      (epoch.recorded ++
        [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩,
        ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, consumedDeposits reset deposited electra, 0⟩])
      queue queue [] [] [] owned after ∧
      OwnershipBefore (eventPosition + (epoch.recorded.length + 2)) paymentPosition after ∧
      after.original = owned.original ∧
      ReserveCut x high ⟨fork, deposited⟩ (getCurrentEpoch deposited) (queue.map (·.entry)) after ∧
      FutureEffectiveCover x ⟨fork, deposited⟩ after ∧ ExitsOrdered deposited ∧
      deposited.slot = s.slot ∧ RegistryLifecycle s deposited ∧
      (∀ (i : Nat) (w : Validator), deposited.validators.data[i]? = some w →
        w.exitEpoch ≠ FAR_FUTURE_EPOCH →
          w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            w.withdrawableEpoch.toNat) ∧
      (ReserveCut x high ⟨fork, deposited⟩ next (queue.map (·.entry)) after →
        (∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
          after.original tag.entry.sourceIndex.toNat = 0) →
        ∃ u suffix consumed payments allocations final,
          TaggedPass next deposited queue u suffix consumed payments ∧
          consolidated.validators = u.validators ∧ consolidated.balances = u.balances ∧
          ReservedReplay (config := config) (checks := checks) x high rounding
            ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, z⟩ next eventPosition paymentPosition
            callPosition
            (epoch.recorded ++
              [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩] ++
              if electra : .pectra ≤ fork then
                [⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
                  consumedDeposits reset deposited electra, 0⟩,
                ⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩,
                  consumedConsolidations deposited consolidated electra,
                  consumedConsolidations deposited consolidated electra⟩]
              else [])
            queue suffix payments allocations [] owned final ∧
          ReservedFrame (config := config) (checks := checks) x high rounding
            ⟨fork, consolidated⟩ ⟨fork, z⟩ next next suffix final final ∧
          OwnershipBefore (eventPosition + (epoch.recorded.length + 3))
            (paymentPosition + payments.length) final ∧
          RetiredActivated z final.retired ∧
          EndpointCoverAll x ⟨fork, z⟩ final ∧ FutureEffectiveCover x ⟨fork, z⟩ final) := by
  have deposits : processPendingDeposits config checks reset electra = .ok deposited := by
    simpa only [EpochStage.Edge, electra, ↓reduceDIte] using depositsOk
  have consolidations : processPendingConsolidations deposited electra = .ok consolidated := by
    simpa only [EpochStage.Edge, electra, ↓reduceDIte] using consolidationsOk
  obtain ⟨after, prefixReplay, prefixFrame, _, counters, matchedD, retiredD, cover, future,
      slotD, lifeD, exitsD, delayedD, activationD, originalSame⟩ :=
    reservedReplay_epochPrefixDeposits_owned (callPosition := callPosition) electra early matched
      epoch deposits reserve
      assignment erasure prior retired startLife startFinite ordered exits finite delayed delayTwo
  refine ⟨after, prefixReplay, counters, originalSame, prefixFrame.2.2.2.2.2.2.2.2,
    future startFuture, exitsD, slotD, lifeD, delayedD, fun reserveNext initialZero => ?_⟩
  have epochD : getCurrentEpoch deposited = getCurrentEpoch s := by
    simp only [getCurrentEpoch, slotD]
  -- The configured delay is at least the two epochs the consolidations read.
  have delayD : ∀ (i : Nat) (w : Validator), deposited.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat := by
    intro i w found assigned
    have := delayedD i w found assigned
    omega
  -- The lifecycle keeps each queued source and its assigned activation.
  have sourcesD : ∀ tag ∈ queue, ∃ w,
      deposited.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
        w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro tag member
    obtain ⟨v, found, assigned⟩ := sources tag member
    obtain ⟨w, located, kept⟩ := lifeD.validators _ v found
    exact ⟨w, located, by rw [kept.activationEpoch assigned]; exact assigned⟩
  have suffixCounters : OwnershipBefore
      (eventPosition + (epoch.recorded ++
        [(⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩ :
        BalanceEvent preset), ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
          consumedDeposits reset deposited electra, 0⟩]).length)
      (paymentPosition + ([] : List (TaggedEntry × Payment preset)).length) after := by
    simpa only [List.length_append, List.length_cons, List.length_nil, List.length_singleton,
      Nat.add_zero] using counters
  obtain ⟨u, suffix, consumed, payments, allocations, final, pass, validators, balances,
      suffixReplay, suffixFrame, suffixCounted, retiredZ, coverZ, futureZ⟩ :=
    reservedReplay_consolidations_suffix
      (callPosition := callPosition + ([] : List (IndexedDepartureCall preset config)).length)
      (credit := consumedConsolidations deposited consolidated electra)
      (debit := consumedConsolidations deposited consolidated electra)
      electra consolidations prefixFrame reserveNext suffixCounters
      (by rw [epochD]; exact nextOk) twoSlots exitsD (activationD activationOrder) delayD caps
      unique apart initialZero (cover startCover) (future startFuture) retiredD sourcesD matchedD
      (by rw [epochD]; exact startCurrent)
      trace
  have joined := prefixReplay.append suffixReplay
  refine ⟨u, suffix, consumed, payments, allocations, final, pass, validators, balances,
    by simpa only [electra, dite_true, List.append_assoc, List.cons_append, List.nil_append,
      List.singleton_append, List.append_nil] using joined, suffixFrame, ?_, retiredZ,
    coverZ, futureZ⟩
  simpa only [List.length_append, List.length_cons, List.length_nil, List.length_singleton,
    Nat.add_zero, Nat.add_assoc] using suffixCounted

/-- The whole-epoch reserved replay, with the initial baselines from the start ownership. -/
private theorem reservedReplay_epochReserved {fork : Fork}
    {s reset deposited consolidated z : BeaconState preset fork}
    {next : Epoch}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (epoch : ReplayedPrefix config checks s reset)
    (depositsOk : EpochStage.Edge config checks .pendingDeposits reset deposited)
    (consolidationsOk : EpochStage.Edge config checks .pendingConsolidations deposited consolidated)
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) consolidated z)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (retired : RetiredActivated s owned.retired)
    (startCover : EndpointCoverAll x ⟨fork, s⟩ owned)
    (startFuture : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (startLife : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (startCurrent : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delayed : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat)
    (delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (caps : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      owned.original tag.entry.sourceIndex.toNat = 0)
    -- The slashed sources' withdrawability from `x` to the consolidation input is a premise.
    --
    -- It is returned unchanged for the reserve.
    (slashedSpan : ∀ (i : Nat) (v w : Validator), x.state.validators.data[i]? = some v →
      deposited.validators.data[i]? = some w → v.slashed = true →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          v.withdrawableEpoch ≤ w.withdrawableEpoch) :
    ∃ after, ReservedReplay (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, deposited⟩ (getCurrentEpoch deposited)
      eventPosition paymentPosition callPosition
      (epoch.recorded ++
        [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩,
        ⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩, consumedDeposits reset deposited electra, 0⟩])
      queue queue [] [] [] owned after ∧
      OwnershipBefore (eventPosition + (epoch.recorded.length + 2)) paymentPosition after ∧
      ReserveCut x high ⟨fork, deposited⟩ (getCurrentEpoch deposited) (queue.map (·.entry)) after ∧
      FutureEffectiveCover x ⟨fork, deposited⟩ after ∧ ExitsOrdered deposited ∧
      deposited.slot = s.slot ∧ RegistryLifecycle x.state deposited ∧
      (∀ (i : Nat) (w : Validator), deposited.validators.data[i]? = some w →
        w.exitEpoch ≠ FAR_FUTURE_EPOCH →
          w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            w.withdrawableEpoch.toNat) ∧
      (∀ (i : Nat) (v w : Validator), x.state.validators.data[i]? = some v →
        deposited.validators.data[i]? = some w → v.slashed = true →
        v.exitEpoch ≠ FAR_FUTURE_EPOCH →
          w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
            v.withdrawableEpoch ≤ w.withdrawableEpoch) ∧
      (ReserveCut x high ⟨fork, deposited⟩ next (queue.map (·.entry)) after →
        ∃ u suffix consumed payments allocations final,
          TaggedPass next deposited queue u suffix consumed payments ∧
          consolidated.validators = u.validators ∧ consolidated.balances = u.balances ∧
          ReservedReplay (config := config) (checks := checks) x high rounding
            ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, z⟩ next eventPosition paymentPosition
            callPosition
            (epoch.recorded ++
              [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩] ++
              if electra : .pectra ≤ fork then
                [⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
                  consumedDeposits reset deposited electra, 0⟩,
                ⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩,
                  consumedConsolidations deposited consolidated electra,
                  consumedConsolidations deposited consolidated electra⟩]
              else [])
            queue suffix payments allocations [] owned final ∧
          ReservedFrame (config := config) (checks := checks) x high rounding
            ⟨fork, consolidated⟩ ⟨fork, z⟩ next next suffix final final ∧
          OwnershipBefore (eventPosition + (epoch.recorded.length + 3))
            (paymentPosition + payments.length) final ∧
          RetiredActivated z final.retired ∧
          EndpointCoverAll x ⟨fork, z⟩ final ∧ FutureEffectiveCover x ⟨fork, z⟩ final) := by
  -- Every prefix step keeps the original balances.
  --
  -- So the ownership at the consolidation input has the start's baselines.
  --
  -- The prefix also gives the current reserve cut and the future cover at that input.
  --
  -- It gives the exit order, the slot, the lifecycle and the exit delay there too.
  --
  -- The caps at the consolidation input come from the caps at `s`.
  --
  -- The steps before the payments keep them.
  --
  -- The pending consolidations keep the registry.
  --
  -- The reserve cut at the next epoch stays the caller's, for that ownership.
  have before := epoch.epochBeforePayments depositsOk consolidationsOk
  have kept : consolidated.validators = deposited.validators :=
    (processPendingConsolidations_kept
      (by simpa only [EpochStage.Edge, electra, ↓reduceDIte] using consolidationsOk)).1
  have capsD : ∀ (i : Nat) (w : Validator), deposited.validators.data[i]? = some w →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w := by
    intro i w found
    apply capped_epochBeforePayments before caps
    rw [kept]
    exact Array.mem_of_getElem? found
  obtain ⟨after, history, counters, originalSame, current, futureD, exitsD, slotD, lifeD,
      delayedD, rest⟩ :=
    reservedReplay_epoch_facts (callPosition := callPosition) electra early matched epoch
      depositsOk consolidationsOk
      trace reserve assignment erasure prior retired startCover startFuture startLife startFinite
      startCurrent ordered exits finite delayed delayTwo activationOrder nextOk twoSlots capsD
      unique apart sources
  refine ⟨after, history, counters, current, futureD, exitsD, slotD, startLife.trans lifeD,
    delayedD, slashedSpan, fun reserveNext => ?_⟩
  exact rest reserveNext (fun tag member n tagged => by
    rw [originalSame]
    exact initialZero tag member n tagged)

/-- The slashed sources' withdrawability from `x` to the consolidation input.

A slashed withdrawable epoch cannot decrease along the run, the cache step and these stages.

This is the slashed-span premise of the reserved replay of the epoch. -/
theorem epochPrefix_slashedSpan {x outer : ForkedBeaconState preset}
    {s reset deposited : BeaconState preset outer.fork} (run : Run config checks x outer)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (cached : processSlot outer.state = .ok s)
    (epoch : EpochPrefix config checks s reset)
    (depositsOk : EpochStage.Edge config checks .pendingDeposits reset deposited) :
    ∀ (i : Nat) (v w : Validator), x.state.validators.data[i]? = some v →
      deposited.validators.data[i]? = some w → v.slashed = true →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          v.withdrawableEpoch ≤ w.withdrawableEpoch :=
  Run.slashed_withdrawableEpoch_mono_epoch run activation compounding cached
    (epoch.depositTrace depositsOk)

/-- Support at the epoch after `c` is support at `c`, or an activation exactly at that epoch.

The epoch before the next one is `c` itself, with no wrap. -/
private theorem supportedAt_next {v : Validator} {c n : Epoch} (step : n.toNat = c.toNat + 1)
    (supported : SupportedAt n v) :
    SupportedAt c v ∨ (v.slashed = false ∧ c < v.activationEpoch ∧ n < v.exitEpoch) := by
  obtain ⟨clean, now | before⟩ := supported
  · simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
      UInt64.le_iff_toNat_le] at now
    by_cases early : v.activationEpoch.toNat ≤ c.toNat
    · refine Or.inl ⟨clean, Or.inl ?_⟩
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
        UInt64.le_iff_toNat_le]
      omega
    · exact Or.inr ⟨clean, UInt64.lt_iff_toNat_lt.mpr (by omega),
        UInt64.lt_iff_toNat_lt.mpr now.2⟩
  · have previous : n - 1 = c := UInt64.toNat_inj.mp (by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp only [UInt64.reduceToNat]
      omega)
    exact Or.inl ⟨clean, Or.inl (previous ▸ before)⟩

/-- Funding relevance at the next epoch is funding relevance at the current one.

A validator that activates at the next epoch has not reached its exit.

So its withdrawable epoch is after the current epoch. -/
private theorem fundingRelevant_next {fork : Fork} {s : BeaconState preset fork} {c n : Epoch}
    {suffix : List PendingConsolidation} {i : Nat} (step : n.toNat = c.toNat + 1)
    (exits : ExitsOrdered s)
    (relevant : FundingRelevant ⟨fork, s⟩ n suffix i) :
    FundingRelevant ⟨fork, s⟩ c suffix i := by
  obtain ⟨v, found, supported | late | queued⟩ := relevant
  · rcases supportedAt_next step supported with old | ⟨_, _, notExited⟩
    · exact ⟨v, found, Or.inl old⟩
    · have ordered := UInt64.le_iff_toNat_le.mp (exits v (Array.mem_of_getElem? found))
      have exitNat := UInt64.lt_iff_toNat_lt.mp notExited
      exact ⟨v, found, Or.inr (Or.inl (UInt64.lt_iff_toNat_lt.mpr (by omega)))⟩
  · have lateNat := UInt64.lt_iff_toNat_lt.mp late
    exact ⟨v, found, Or.inr (Or.inl (UInt64.lt_iff_toNat_lt.mpr (by omega)))⟩
  · exact ⟨v, found, Or.inr (Or.inr queued)⟩

/-- The reserve cut at the current epoch gives the cut at the next epoch.

It needs two provenance facts for sources that become due, and the future cover. -/
private theorem reserveCut_next {x : ForkedBeaconState preset} {fork : Fork}
    {s : BeaconState preset fork} {high : Nat} {next : Epoch}
    {suffix : List PendingConsolidation} {owned : Ownership}
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (exits : ExitsOrdered s)
    (start : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    -- A source of the start's queue due by the next epoch is initially pending.
    --
    -- So the pending clause bounds it.
    (initialDue : ∀ q ∈ suffix,
      (∃ p ∈ pendingQueue x, p.sourceIndex.toNat = q.sourceIndex.toNat) →
      ∀ v, s.validators.data[q.sourceIndex.toNat]? = some v → v.withdrawableEpoch ≤ next →
        InitialPending x high q.sourceIndex.toNat)
    -- Take a source queued later, due by the next epoch and no new reference.
    --
    -- It was inactive at the start, so the idle clause bounds it.
    (freshDue : ∀ q ∈ suffix,
      (¬ ∃ p ∈ pendingQueue x, p.sourceIndex.toNat = q.sourceIndex.toNat) →
      ¬ NewReference x q.sourceIndex.toNat →
      ∀ v, s.validators.data[q.sourceIndex.toNat]? = some v → v.withdrawableEpoch ≤ next →
        (x.state.validators.data[q.sourceIndex.toNat]?).all (fun initial =>
          !isActiveValidator initial (getCurrentEpoch x.state) &&
            !isActiveValidator initial (getPreviousEpoch x.state)))
    -- Take a validator that activates at the next epoch.
    --
    -- Its effective balance is covered at the endpoint.
    --
    -- The endpoint clause needs this, and no clause at the current epoch gives it.
    (future : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) suffix owned) :
    ReserveCut x high ⟨fork, s⟩ next suffix owned := by
  -- Every other clause reads the demand epoch only through three things.
  --
  -- They are support, funding relevance and an activation or exit after it.
  --
  -- Each of them moves from the next epoch back to the current one.
  have step : next.toNat = (getCurrentEpoch s).toNat + 1 := by
    simpa only [UInt64.reduceToNat] using (Uint64.addChecked_ok_iff.mp nextOk).2
  have earlier : getCurrentEpoch s ≤ next := UInt64.le_iff_toNat_le.mpr (by omega)
  have startNat := UInt64.le_iff_toNat_le.mp start
  obtain ⟨valid, wasRetired, original, reference, scheduled, pending, _, idle,
    activePending, endpoint⟩ := reserve
  refine ⟨valid, ?_, original, fun i ref notRetired support =>
    reference i ref notRetired (fundingRelevant_next step exits support), ?_,
    fun i initial notRetired support =>
      pending i initial notRetired (fundingRelevant_next step exits support), ?_, ?_,
    fun i initial v old located current active notRetired support =>
      activePending i initial v old located current active notRetired
        (fundingRelevant_next step exits support), ?_⟩
  · intro i member v found
    obtain ⟨unsupported, absent⟩ := wasRetired i member v found
    exact ⟨fun e later => unsupported e (UInt64.le_trans earlier later), absent⟩
  · intro i initial v found active clean finite located ⟨e, later, supported⟩
    exact scheduled i initial v found active clean finite located
      ⟨e, UInt64.le_trans earlier later, supported⟩
  -- A queued source that is due is bounded by the pending clause or by the idle clause.
  · intro q member v found ready notRef
    by_cases queuedAtStart : ∃ p ∈ pendingQueue x, p.sourceIndex.toNat = q.sourceIndex.toNat
    · have initial := initialDue q member queuedAtStart v found ready
      have notRetired : q.sourceIndex.toNat ∉ owned.retired := fun retired =>
        (wasRetired _ retired v found).2 ⟨q, member, rfl⟩
      exact pending _ initial notRetired ⟨v, found, Or.inr (Or.inr ⟨q, member, rfl⟩)⟩ v found
    · have quiet := freshDue q member queuedAtStart notRef v found ready
      exact Nat.le_trans (Nat.le_max_right _ _)
        (idle _ v found notRef queuedAtStart quiet (Or.inr (Or.inr ⟨⟨q, member, rfl⟩,
          queuedAtStart⟩)))
  · intro i v found notRef notPending quiet support
    refine idle i v found notRef notPending quiet ?_
    rcases support with supported | ⟨waiting, notExited⟩ | queued
    · rcases supportedAt_next step supported with old | ⟨_, activates, notExited⟩
      · exact Or.inl old
      · have exitNat := UInt64.lt_iff_toNat_lt.mp notExited
        exact Or.inr (Or.inl ⟨activates, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩)
    · have waitNat := UInt64.lt_iff_toNat_lt.mp waiting
      have exitNat := UInt64.lt_iff_toNat_lt.mp notExited
      exact Or.inr (Or.inl ⟨UInt64.lt_iff_toNat_lt.mpr (by omega),
        UInt64.lt_iff_toNat_lt.mpr (by omega)⟩)
    · exact Or.inr (Or.inr queued)
  -- A validator activating at the next epoch is covered by the future cover.
  · intro i v found supported notPrevious
    rcases supportedAt_next step supported with old | ⟨clean, activates, notExited⟩
    · exact endpoint i v found old notPrevious
    · have exitNat := UInt64.lt_iff_toNat_lt.mp notExited
      exact future i v found activates clean (UInt64.lt_iff_toNat_lt.mpr (by omega))

/-- The reserve cut at the next epoch, at the pending-consolidation input `u` of an epoch.

Let every queued source that becomes due be bounded.

Then the cut at the current epoch moves to the next one.

The move of the cut to the next epoch asks for this bound in two cases. -/
private theorem reserveCut_next_of_provenance {x : ForkedBeaconState preset} {fork : Fork}
    {u : BeaconState preset fork} {high : Nat} {next : Epoch} {queue : List TaggedEntry}
    {owned : Ownership}
    (nextOk : Uint64.addChecked (getCurrentEpoch u) 1 = .ok next)
    (horizon : next.toNat ≤ horizonEnd x high)
    (exits : ExitsOrdered u)
    (start : getCurrentEpoch x.state ≤ getCurrentEpoch u)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (life : RegistryLifecycle x.state u)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state)
    (slashedExit : ∀ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v →
      v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (delayed : ∀ (i : Nat) (w : Validator), u.validators.data[i]? = some w →
      w.exitEpoch ≠ FAR_FUTURE_EPOCH →
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          w.withdrawableEpoch.toNat)
    (slashedLater : ∀ (i : Nat) (v w : Validator), x.state.validators.data[i]? = some v →
      u.validators.data[i]? = some w → v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.withdrawableEpoch ≤ w.withdrawableEpoch)
    (provenance : ∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
      (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH))
    (future : FutureEffectiveCover x ⟨fork, u⟩ owned)
    (reserve : ReserveCut x high ⟨fork, u⟩ (getCurrentEpoch u) (queue.map (·.entry)) owned) :
    ReserveCut x high ⟨fork, u⟩ next (queue.map (·.entry)) owned := by
  refine reserveCut_next nextOk exits start ?_ ?_ future reserve
  -- The first case is a source of the start's queue, which has its exit assigned at `x`.
  --
  -- If it is unslashed at `x`, it withdraws there at most the delay after its exit.
  --
  -- The exit stays the same up to `u`, where the delay is at least met.
  --
  -- So the withdrawable epoch at `x` is at most the one at `u`.
  --
  -- If it is slashed at `x`, its withdrawable epoch does not decrease up to `u`.
  --
  -- Either way the source is due by `next`, and so by the horizon, already at `x`.
  --
  -- A source of the start's queue that is due by `next` is initially pending.
  · intro q _ ⟨p, queued, sameIndex⟩ v found ready
    unfold pendingQueue at queued
    split at queued
    case isFalse => simp at queued
    rename_i electra
    obtain ⟨initial, initialAt, _, delayedAt, assigned⟩ := (ordered.1 electra).2 p queued
    obtain ⟨_, unslashedExact, _⟩ := (ordered.2 electra).2 p queued initial initialAt
    rw [sameIndex] at initialAt
    refine ⟨p, by simpa only [pendingQueue, electra, ↓reduceDIte] using queued, sameIndex, ?_⟩
    rw [← sameIndex, show p.sourceIndex.toNat = q.sourceIndex.toNat from sameIndex, initialAt]
    simp only [Option.map_some, Option.getD_some]
    have readyNat := UInt64.le_iff_toNat_le.mp ready
    cases flag : initial.slashed
    · -- The exit is kept up to `u`, where the delay is at least met.
      obtain ⟨later, located, epochs⟩ := life.validators _ initial initialAt
      obtain rfl := Option.some.inj (located.symm.trans found)
      have sameExit := epochs.exitEpoch assigned
      have atU := delayed _ later located (sameExit ▸ assigned)
      have atX := unslashedExact flag
      rw [sameExit] at atU
      omega
    · have grown :=
        UInt64.le_iff_toNat_le.mp (slashedLater _ initial v initialAt found flag assigned)
      omega
  -- The second case is any other queued source, which had an unset exit at `x`.
  --
  -- That follows from the queue provenance.
  --
  -- At `x` a slashed key has its exit assigned, so this source was unslashed at `x`.
  --
  -- A source that is no new reference was then inactive at `x`, read at `x` itself.
  --
  -- A later slashing of the source does not enter: only the source at `x` is read.
  --
  -- Any other queued source had an unset exit at `x`, so it was unslashed and inactive there.
  · intro q member notQueued notReference v _ _
    rcases provenance q member with queued | unset
    · exact absurd ⟨q, queued, rfl⟩ notQueued
    cases initial : x.state.validators.data[q.sourceIndex.toNat]? with
    | none => simp
    | some w =>
      rw [initial] at unset
      simp only [Option.all_some, beq_iff_eq] at unset
      have clean : w.slashed = false := by
        cases flag : w.slashed
        · rfl
        · exact absurd unset (slashedExit _ w initial flag)
      have inactive := nonreference_before_unset_exit (u := x) (RegistryLifecycle.refl _)
        (SlashedPersistence.refl _) initial unset clean finite notReference
      rw [initial] at inactive
      exact inactive

/-- The whole-epoch reserved replay, with the reserve cut at the next epoch supplied. -/
theorem reservedReplay_epochNext {fork : Fork}
    {s reset deposited consolidated z : BeaconState preset fork}
    {next : Epoch}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (epoch : ReplayedPrefix config checks s reset)
    (depositsOk : EpochStage.Edge config checks .pendingDeposits reset deposited)
    (consolidationsOk : EpochStage.Edge config checks .pendingConsolidations deposited consolidated)
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) consolidated z)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (retired : RetiredActivated s owned.retired)
    (startCover : EndpointCoverAll x ⟨fork, s⟩ owned)
    (startFuture : FutureEffectiveCover x ⟨fork, s⟩ owned)
    (startLife : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (startCurrent : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delayed : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat)
    (delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationOrder : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (caps : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v)
    (unique : (queue.map (fun tag => tag.entry.sourceIndex)).Nodup)
    (apart : ∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex)
    (sources : ∀ tag ∈ queue, ∃ w, s.validators.data[tag.entry.sourceIndex.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      owned.original tag.entry.sourceIndex.toNat = 0)
    (slashedSpan : ∀ (i : Nat) (v w : Validator), x.state.validators.data[i]? = some v →
      deposited.validators.data[i]? = some w → v.slashed = true →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        w.slashed = true ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          v.withdrawableEpoch ≤ w.withdrawableEpoch)
    (horizon : next.toNat ≤ horizonEnd x high)
    (orderedX : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state)
    (slashedExit : ∀ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v →
      v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (provenance : ∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
      (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) :
        ∃ u suffix consumed payments allocations final,
          TaggedPass next deposited queue u suffix consumed payments ∧
          consolidated.validators = u.validators ∧ consolidated.balances = u.balances ∧
          ReservedReplay (config := config) (checks := checks) x high rounding
            ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, z⟩ next eventPosition paymentPosition
            callPosition
            (epoch.recorded ++
              [⟨.slashings, ⟨fork, epoch.registered⟩, ⟨fork, epoch.slashed⟩, 0, epoch.limit⟩] ++
              if electra : .pectra ≤ fork then
                [⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
                  consumedDeposits reset deposited electra, 0⟩,
                ⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩,
                  consumedConsolidations deposited consolidated electra,
                  consumedConsolidations deposited consolidated electra⟩]
              else [])
            queue suffix payments allocations [] owned final ∧
          ReservedFrame (config := config) (checks := checks) x high rounding
            ⟨fork, consolidated⟩ ⟨fork, z⟩ next next suffix final final ∧
          OwnershipBefore (eventPosition + (epoch.recorded.length + 3))
            (paymentPosition + payments.length) final ∧
          RetiredActivated z final.retired ∧
          EndpointCoverAll x ⟨fork, z⟩ final ∧ FutureEffectiveCover x ⟨fork, z⟩ final := by
  -- The composition gives several facts at the consolidation input and for its own ownership.
  --
  -- They are the current cut, the future cover, the exit order and the slot.
  --
  -- They also include the registry lifecycle from `x`, the withdrawal delay and the slashed span.
  --
  -- The lemma above on the cut at the next epoch turns these into that cut.
  --
  -- It also uses the queue provenance and the queue order at `x`.
  --
  -- It also uses the assigned exits of slashed keys at `x` and the horizon.
  obtain ⟨_, _, _, current, futureD, exitsD, slotD, lifeD, delayedD, spanD, rest⟩ :=
    reservedReplay_epochReserved (callPosition := callPosition) electra early matched epoch
      depositsOk consolidationsOk
        trace reserve assignment erasure prior retired startCover startFuture startLife startFinite
        startCurrent ordered exits finite delayed delayTwo activationOrder nextOk twoSlots caps
        unique apart sources initialZero slashedSpan
  -- The consolidation input is in the epoch of `s`.
  have epochD : getCurrentEpoch deposited = getCurrentEpoch s := by
    simp only [getCurrentEpoch, slotD]
  exact rest (reserveCut_next_of_provenance (by rw [epochD]; exact nextOk) horizon exitsD
    (by rw [epochD]; exact startCurrent) startFinite lifeD orderedX slashedExit delayedD
    (fun i v w initial later flag assigned => (spanD i v w initial later flag assigned).2.2)
    provenance futureD current)

/-- The queue provenance at the end of the run's replay history from `x`.

The history starts from the initial tags of `x`'s queue, whose entries are that queue.

Each recorded event of the run has the registry lifecycle from `x` to its state.

So each event keeps the provenance. -/
theorem run_queue_provenance {g x outer : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x outer)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : outer.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch outer.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : pre.balanceEvents high = .ok events)
    (electraX : .pectra ≤ x.fork)
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition events
      (initialTags (x.state.pendingConsolidations electraX).data.toList) queue
      payments allocations calls before after)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    ∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
      (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH) := by
  refine (history.counters_provenance prior).2
    (fun e member =>
      (replay_event_provenance shared pre genesis early high endEpoch events replayed e member).1)
    ?_
  -- The initial tags carry exactly the entries of `x`'s queue.
  intro c member
  left
  simp only [initialTags, List.map_map] at member
  simpa only [pendingQueue, electraX, ↓reduceDIte] using
    (by simpa [Function.comp_def] using member : c ∈
          (x.state.pendingConsolidations electraX).data.toList)

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
