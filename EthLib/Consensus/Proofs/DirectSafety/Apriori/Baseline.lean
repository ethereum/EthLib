module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly

/-!
# The original baseline

Along a branch the original effective balance of a key only drops.

It stays within one increment of the effective balance after its first drop.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-! ## Lowering the original baseline -/

/-- The paid reserve split `P = max(e, b) = R + C` keeps `R` nonincreasing.

Here `R' = min(R, P')`, with `P'` read at `u`.

Only the original baselines change. -/
def lowerOriginal (o : Ownership) (u : ForkedBeaconState preset) : Ownership :=
  { o with original := fun i => min (o.original i) (max (effectiveAt u i) (actualBalanceAt u i)) }

/-- The lowering mints, moves, retires and endpoints nothing, and only lowers original baselines. -/
private theorem lowerOriginal_frame (o : Ownership) (u : ForkedBeaconState preset) :
    (lowerOriginal o u).issued = o.issued ∧ (lowerOriginal o u).owner = o.owner ∧
    (lowerOriginal o u).endpoint = o.endpoint ∧ (lowerOriginal o u).retired = o.retired ∧
    (∀ i, (lowerOriginal o u).original i ≤ o.original i) ∧
    (OwnershipValid o → OwnedFrame o (lowerOriginal o u)) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => Nat.min_le_left _ _, fun valid =>
    ⟨valid, valid, rfl, fun _ => .inl rfl, Finset.Subset.refl _, rfl,
      fun _ => Nat.min_le_left _ _⟩⟩

/-- Lowering at the cut's own state keeps the cut.

Only the reference clause has the original baseline on its larger side.

The lowered value is either the old one or the funding value itself.

That funding value is the larger of the effective balance and the balance at `u`.

It is at least the potential, which caps the balance before it takes the larger. -/
private theorem reserveCut_lowerOriginal {x : ForkedBeaconState preset} {high : Nat}
    {u : ForkedBeaconState preset} {demandEpoch : Epoch} {suffix : List PendingConsolidation}
    {o : Ownership} (reserve : ReserveCut x high u demandEpoch suffix o) :
    ReserveCut x high u demandEpoch suffix (lowerOriginal o u) := by
  obtain ⟨valid, wasRetired, original, reference, rest⟩ := reserve
  refine ⟨valid, wasRetired, fun i => ⟨(Nat.min_le_left _ _).trans (original i).1,
    fun notReference => ?_⟩, fun i ref notRetired relevant => ?_, rest⟩
  · show min (o.original i) _ = 0
    rw [(original i).2 notReference, Nat.zero_min]
  · have old := reference i ref notRetired relevant
    -- The potential is at most the funding value, since the capped balance is at most the balance.
    have capped : potential u i ≤ max (effectiveAt u i) (actualBalanceAt u i) := by
      unfold potential effectiveAt
      cases u.state.validators.data[i]? <;> simp
      omega
    show potential u i ≤
      min (o.original i) (max (effectiveAt u i) (actualBalanceAt u i)) + (held o i).card
    omega

/-- Lowering at a state is a reserved frame from that state to itself. -/
private theorem reservedFrame_lowerOriginal {x u : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {epoch : Epoch} {queue : List TaggedEntry} {owned : Ownership}
    (reserve : ReserveCut x high u epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue u)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      u u epoch epoch queue owned (lowerOriginal owned u) :=
  ⟨.nil, UInt64.le_refl _, (lowerOriginal_frame owned u).2.2.2.2.2 reserve.1, assignment,
    assignmentCut_transport assignment (lowerOriginal_frame owned u).2.2.2.2.1
      (List.Sublist.refl _),
    erasure, erasure, reserve, reserveCut_lowerOriginal reserve⟩

/-- A downward effective-balance update rounds the balance down.

Afterwards the balance is below the new effective balance plus one increment.

The caps rule out the capped branch. -/
private theorem effective_drop_balance_lt {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t)
    (caps : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (i : Nat)
    (drop : effectiveAt ⟨fork, t⟩ i < effectiveAt ⟨fork, s⟩ i) :
    actualBalanceAt ⟨fork, s⟩ i <
      effectiveAt ⟨fork, t⟩ i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  cases read : s.balances.data[i]? with
  | none => simp only [actualBalanceAt, read, Option.map_none, Option.getD_none]; omega
  | some b =>
    cases found : s.validators.data[i]? with
    | none => simp [effectiveAt, found] at drop
    | some v =>
      obtain ⟨e, after, updated⟩ :=
        processEffectiveBalanceUpdates_effectiveBalance_eq ok found read
      have cap := UInt64.le_iff_toNat_le.mp (caps v (Array.mem_of_getElem? found))
      simp only [effectiveAt, after, found, Option.map_some, Option.getD_some] at drop ⊢
      simp only [actualBalanceAt, read, Option.map_some, Option.getD_some]
      rcases updatedEffectiveBalance_cases updated with same | rounded
      · subst same
        exact absurd drop (Nat.lt_irrefl _)
      · have r := toNat_rounded (preset := preset) (balance := b)
        have m1 := Nat.mod_lt b.toNat increment
        have m2 := Nat.mod_le b.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        rw [rounded, UInt64.min_def] at drop ⊢
        by_cases small : b - b % preset.EFFECTIVE_BALANCE_INCREMENT ≤
            withdrawalMaxEffectiveBalance preset fork v
        · rw [ite_eq_left small] at drop ⊢
          rw [r]
          omega
        · rw [ite_eq_right small] at drop
          omega

/-- The epoch suffix after the pending consolidations, before Gloas.

Its payments stage keeps the state.

Its effective-balance update reads the consolidation output.

Its later stages keep the validators and the balances. -/
private theorem epochSuffix_effective {fork : Fork} {consolidated z : BeaconState preset fork}
    (early : fork < .glamsterdam)
    (trace : EpochTrace (EpochStage.action config checks)
      (EpochStage.middleStages ++ EpochStage.tailStages) consolidated z) :
    ∃ after, processEffectiveBalanceUpdates consolidated = .ok after ∧
      z.validators = after.validators ∧ z.balances = consolidated.balances := by
  simp only [EpochStage.middleStages, EpochStage.tailStages, List.cons_append,
    List.nil_append] at trace
  cases trace with | cons paid trace =>
  cases trace with | cons updated rest =>
  have payEdge := EpochStage.action_cases.mp paid
  simp only [EpochStage.Edge] at payEdge
  split at payEdge
  · rename_i late
    exact absurd (Nat.lt_of_le_of_lt late early) (Nat.lt_irrefl _)
  subst payEdge
  have updatedOk : processEffectiveBalanceUpdates _ = .ok _ :=
    EpochStage.action_cases.mp updated
  have late := balanceDrift_late rest
  exact ⟨_, updatedOk, late.1, late.2.trans (processEffectiveBalanceUpdates_balances updatedOk)⟩

/-- The whole-epoch reserved replay, followed by the lowering at its end state `z`.

Its header is unchanged.

This wrapper appends the lowering frame at `z` to its replay and to its suffix frame.

The last conjunct is the effective bound that the carried bound on original baselines reads.

Without a drop, the lowered value is at most the old one.

A drop rounds the balance down.

So the lowered value is below the new effective balance plus one increment. -/
theorem reservedReplay_epochNext_lowered {fork : Fork}
    {s justified scored rewarded registered slashed reset deposited consolidated z :
      BeaconState preset fork}
    {recorded : List (BalanceEvent preset)} {limit : Nat} {next : Epoch}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (justifiedOk : EpochStage.Edge config checks .justification s justified)
    (scoredOk : EpochStage.Edge config checks .inactivity justified scored)
    (rewardsOk : processRewardsAndPenalties config scored = .ok rewarded)
    (replay : replayRewards (config := config) (scored, []) = .ok (rewarded, recorded))
    (registry : processRegistryUpdates config rewarded = .ok registered)
    (slashings : processSlashings registered = .ok slashed)
    (limitOk : delayedSlashingLimit registered = .ok limit)
    (resetOk : EpochStage.Edge config checks .eth1Reset slashed reset)
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
            (recorded ++ [⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩] ++
              if electra : .pectra ≤ fork then
                [⟨.deposits, ⟨fork, reset⟩, ⟨fork, deposited⟩,
                  consumedDeposits reset deposited electra, 0⟩,
                ⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩,
                  consumedConsolidations deposited consolidated electra,
                  consumedConsolidations deposited consolidated electra⟩]
              else [])
            queue suffix payments allocations [] owned
              (lowerOriginal final ⟨fork, z⟩) ∧
          ReservedFrame (config := config) (checks := checks) x high rounding
            ⟨fork, consolidated⟩ ⟨fork, z⟩ next next suffix final
              (lowerOriginal final ⟨fork, z⟩) ∧
          OwnershipBefore (eventPosition + (recorded.length + 3))
            (paymentPosition + payments.length) (lowerOriginal final ⟨fork, z⟩) ∧
          RetiredActivated z (lowerOriginal final ⟨fork, z⟩).retired ∧
          EndpointCoverAll x ⟨fork, z⟩ (lowerOriginal final ⟨fork, z⟩) ∧
          FutureEffectiveCover x ⟨fork, z⟩ (lowerOriginal final ⟨fork, z⟩) ∧
          (0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat → ∀ down : Nat → Prop,
            (∀ i, owned.original i ≤ effectiveAt ⟨fork, s⟩ i +
              (if down i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) →
            ∀ i, (lowerOriginal final ⟨fork, z⟩).original i ≤ effectiveAt ⟨fork, z⟩ i +
              (if down i ∨ effectiveAt ⟨fork, z⟩ i < effectiveAt ⟨fork, s⟩ i then
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  obtain ⟨u, suffix, consumed, payments, allocations, final, pass, validators, balances, history,
      frame, counted, retiredZ, coverZ, futureZ⟩ :=
    reservedReplay_epochNext (callPosition := callPosition) electra early matched justifiedOk
      scoredOk rewardsOk replay registry slashings limitOk resetOk depositsOk consolidationsOk
      trace reserve assignment erasure prior retired startCover startFuture startLife startFinite
      startCurrent ordered exits finite delayed delayTwo activationOrder nextOk twoSlots caps
      unique apart sources initialZero slashedSpan horizon orderedX slashedExit provenance
  have lower := reservedFrame_lowerOriginal (config := config) (checks := checks)
    frame.2.2.2.2.2.2.2.2 frame.2.2.2.2.1 frame.2.2.2.2.2.2.1
  refine ⟨u, suffix, consumed, payments, allocations, final, pass, validators, balances, ?_,
    frame.trans lower, counted, retiredZ, coverZ, futureZ, ?_⟩
  · simpa only [List.append_nil] using history.append (ReservedReplay.nil lower)
  · intro increment down before i
    -- The prefix keeps effective balances and caps up to the consolidation output.
    have prefixOk : epochBeforePayments config checks s = .ok consolidated := by
      rw [epochBeforePayments_eq_run]
      exact EpochTrace.run_ok_iff.mpr ((EpochTrace.append_iff
        (xs := [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
          .pendingDeposits]) (ys := [.pendingConsolidations])).mpr
        ⟨deposited, epochDepositTrace justifiedOk scoredOk rewardsOk registry slashings resetOk
          depositsOk, .cons (EpochStage.action_cases.mpr consolidationsOk) .nil⟩)
    have kept := effectiveKept_epochBeforePayments prefixOk
    have capsC := capped_epochBeforePayments prefixOk caps
    obtain ⟨q, updated, zValidators, zBalances⟩ := epochSuffix_effective early trace
    have lowered : final.original i ≤ owned.original i := history.counters_original.2.2.1 i
    have zEffective : effectiveAt ⟨fork, z⟩ i = effectiveAt ⟨fork, q⟩ i := by
      simp only [effectiveAt, zValidators]
    have zBalance : actualBalanceAt ⟨fork, z⟩ i = actualBalanceAt ⟨fork, consolidated⟩ i := by
      simp only [actualBalanceAt, zBalances]
    have prior := before i
    show min (final.original i) (max (effectiveAt ⟨fork, z⟩ i) (actualBalanceAt ⟨fork, z⟩ i)) ≤ _
    by_cases drop : effectiveAt ⟨fork, z⟩ i < effectiveAt ⟨fork, s⟩ i
    · have inside : i < s.validators.data.size := by
        by_contra outside
        have none : s.validators.data[i]? = none :=
          Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt outside)
        simp [effectiveAt, none] at drop
      have same := kept i inside
      have dropC : effectiveAt ⟨fork, q⟩ i < effectiveAt ⟨fork, consolidated⟩ i := by omega
      have bound := effective_drop_balance_lt updated capsC increment i dropC
      rw [ite_eq_left (Or.inr drop)]
      omega
    · by_cases flagged : down i
      · rw [ite_eq_left (Or.inl flagged)]
        rw [ite_eq_left flagged] at prior
        omega
      · rw [ite_eq_right (fun h => h.elim flagged drop)]
        rw [ite_eq_right flagged] at prior
        omega

/-! ## The carried bound and the assignment premise -/

/-- The carried bound: each original baseline is at most the effective balance at the run's end.

A key with a first drop on the run may exceed it by one increment. -/
def OriginalDown {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (o : Ownership) : Prop :=
  ∀ i, o.original i ≤ effectiveAt y i +
    (if FirstDown tail i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)

/-- A first drop is any drop: the earliest one has no drop before it. -/
private theorem firstDown_iff_pathDrop {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : Nat) :
    FirstDown tail i ↔ PathDrop tail.balancePath i := by
  constructor
  · rintro ⟨j, a, b, one, two, less, _⟩
    exact ⟨j, a, b, one, two, less⟩
  · intro exists'
    obtain ⟨a, b, one, two, less⟩ := Nat.find_spec exists'
    refine ⟨Nat.find exists', a, b, one, two, less, ?_⟩
    intro k u v earlier ku kv
    by_contra up
    exact Nat.find_min exists' earlier ⟨u, v, ku, kv, by omega⟩

private theorem pathDrop_append_left {path more : List (ForkedBeaconState preset)} {i : Nat}
    (drop : PathDrop path i) : PathDrop (path ++ more) i := by
  obtain ⟨j, a, b, one, two, less⟩ := drop
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp two
  refine ⟨j, a, b, ?_, ?_, less⟩
  · rw [List.getElem?_append_left (by omega)]
    exact one
  · rw [List.getElem?_append_left inside]
    exact two

/-- Two paths that meet at one state drop together exactly where one of them drops. -/
private theorem pathDrop_append_iff {path more : List (ForkedBeaconState preset)} {i : Nat}
    {c : ForkedBeaconState preset} (last : path.getLast? = some c) (head : more.head? = some c) :
    PathDrop (path ++ more) i ↔ PathDrop path i ∨ PathDrop more i := by
  constructor
  · rintro ⟨j, a, b, one, two, less⟩
    have lastAt : path[path.length - 1]? = some c := by
      rw [← List.getLast?_eq_getElem?]
      exact last
    have headAt : more[0]? = some c := by
      rw [← List.head?_eq_getElem?]
      exact head
    have nonempty : 0 < path.length := by
      cases path with
      | nil => simp at last
      | cons _ _ => simp
    by_cases early : j + 1 < path.length
    · left
      refine ⟨j, a, b, ?_, ?_, less⟩
      · rwa [List.getElem?_append_left (by omega)] at one
      · rwa [List.getElem?_append_left early] at two
    · by_cases late : path.length ≤ j
      · right
        refine ⟨j - path.length, a, b, ?_, ?_, less⟩
        · rwa [List.getElem?_append_right late] at one
        · rw [List.getElem?_append_right (by omega)] at two
          rwa [show j + 1 - path.length = j - path.length + 1 by omega] at two
      · exfalso
        have atJ : j = path.length - 1 := by omega
        rw [List.getElem?_append_left (by omega), atJ, lastAt] at one
        rw [List.getElem?_append_right (by omega),
          show j + 1 - path.length = 0 by omega, headAt] at two
        cases one
        cases two
        exact Nat.lt_irrefl _ less
  · rintro (drop | ⟨j, a, b, one, two, less⟩)
    · exact pathDrop_append_left drop
    · refine ⟨path.length + j, a, b, ?_, ?_, less⟩
      · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        exact one
      · rw [List.getElem?_append_right (by omega),
          show path.length + j + 1 - path.length = j + 1 by omega]
        exact two

/-- A first drop of a prefix is a first drop of every extension. -/
private theorem firstDown_append {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (rest : Run config checks m y) (i : Nat)
    (drop : FirstDown pre i) : FirstDown (pre.append rest) i := by
  rw [firstDown_iff_pathDrop] at drop ⊢
  rw [Run.balancePath_append]
  exact pathDrop_append_left drop

/-- A drop in the whole run is a drop in the prefix or in the last step. -/
private theorem firstDown_snoc_iff {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m n) (i : Nat) :
    FirstDown (pre.snoc step) i ↔ FirstDown pre i ∨ StepDrop step i := by
  rw [firstDown_iff_pathDrop, firstDown_iff_pathDrop]
  exact pathDrop_append_iff (Run.balancePath_ends pre).2 (Step.balancePath_ends step).1

/-- Base of the carried bound, from the original baselines of the initial ownership. -/
theorem originalDown_initial {x : ForkedBeaconState preset} {high : Nat} {o : Ownership}
    (initial : OwnedInitial x high o) : OriginalDown (Run.nil : Run config checks x x) o := by
  intro i
  rw [initial.2.2.2.2.2 i]
  split <;> (split <;> omega)

/-- A block step keeps the bound: effective balances are kept and original baselines only drop. -/
theorem originalDown_block {x : ForkedBeaconState preset} {fork : Fork}
    {m n : BeaconState preset fork}
    (pre : Run config checks x ⟨fork, m⟩) (step : Step config checks ⟨fork, m⟩ ⟨fork, n⟩)
    {o o' : Ownership} (down : OriginalDown pre o) (kept : EffectiveKept m n)
    (lower : ∀ i, o'.original i ≤ o.original i) : OriginalDown (pre.snoc step) o' := by
  intro i
  have d := down i
  have l := lower i
  have effective : effectiveAt ⟨fork, m⟩ i ≤ effectiveAt ⟨fork, n⟩ i := by
    by_cases inside : i < m.validators.data.size
    · exact (kept i inside).ge
    · have none : m.validators.data[i]? = none :=
        Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt inside)
      simp [effectiveAt, none]
  by_cases f : FirstDown pre i
  · rw [ite_eq_left f] at d
    rw [ite_eq_left ((firstDown_snoc_iff pre step i).mpr (.inl f))]
    omega
  · rw [ite_eq_right f] at d
    split <;> omega

/-- A slot step keeps the bound, given the effective-balance bound of the slot replay. -/
theorem originalDown_slot {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m n) {o o' : Ownership}
    (down : OriginalDown pre o)
    (bound : ∀ down : Nat → Prop,
      (∀ i, o.original i ≤ effectiveAt m i +
        (if down i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) →
      ∀ i, o'.original i ≤ effectiveAt n i +
        (if down i ∨ StepDrop step i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) :
    OriginalDown (pre.snoc step) o' := by
  intro i
  have h := bound (FirstDown pre) down i
  by_cases f : FirstDown pre i ∨ StepDrop step i
  · rw [ite_eq_left f] at h
    rw [ite_eq_left ((firstDown_snoc_iff pre step i).mpr f)]
    exact h
  · rw [ite_eq_right f] at h
    omega

/-- A key whose exit a step assigns, after a first drop, is a source-falling key.

Its stop holds a charge, since its exit goes from FAR at `x` to assigned at `y`.

The stop's assigning step cannot lie inside `pre`, where the exit is still FAR at its end.

Nor can it be `pre` itself.

So `pre` is a prefix of the stop's run.

The key is unslashed at its stop state, since its exit is still FAR there. -/
theorem RoundLedger.sourceFalling_of_firstDown
    {g x y m n : ForkedBeaconState preset} {high : Nat} {tail : Run config checks x y}
    (ledger : RoundLedger tail high) (shared : Run config checks g x)
    (supported : Supported shared tail high)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (pre : Run config checks x m) (step : Step config checks m n)
    (rest : Run config checks n y) (split : (pre.snoc step).append rest = tail)
    (i : Nat) (v w : Validator) (before : m.state.validators.data[i]? = some v)
    (after : n.state.validators.data[i]? = some w)
    (unset : v.exitEpoch = FAR_FUTURE_EPOCH) (assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (reference : NewReference x i) (drop : FirstDown pre i) : i ∈ ledger.sourceFalling := by
  obtain ⟨initial, initialFound, initialUnset⟩ : ∃ u, x.state.validators.data[i]? = some u ∧
      u.exitEpoch = FAR_FUTURE_EPOCH := by
    unfold NewReference at reference
    cases h : x.state.validators.data[i]? with
    | none => simp [h] at reference
    | some u =>
      simp only [h, Option.any_some, Bool.and_eq_true, beq_iff_eq] at reference
      exact ⟨u, rfl, reference.2⟩
  obtain ⟨final, finalFound, finalLife⟩ := rest.registryLifecycle.validators i w after
  have finalAssigned : final.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [finalLife.exitEpoch assigned]
    exact assigned
  obtain ⟨c, chosen, _⟩ :=
    (ledger.stops i).charge_of_new_exit initialFound finalFound initialUnset finalAssigned
  have selected := (ledger.stops i).selected
  rw [chosen] at selected
  obtain ⟨_, _, _, next, assigning, remaining, split₂, _, v', w', atStop, atNext, unset',
    assigned', _⟩ := selected
  have caps := supported.2.2.1
  have early : (ledger.stops i).state.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps (ledger.stops i).post.chainSteps)
      supported.2.2.2.2.1
  have clean : v'.slashed = false := by
    cases flag : v'.slashed
    · rfl
    · exact absurd unset' (run_slashed_exit_assigned (shared.append (ledger.stops i).pre)
        supported.1 caps.activation caps.compounding delay i v' atStop flag)
  have split₁ := (pre.snoc_append_eq step rest).symm.trans split
  have firstDown : FirstDown (ledger.stops i).pre i := by
    rcases Run.prefix_total pre _ ((ledger.stops i).pre.snoc assigning) remaining split₁ split₂
      with ⟨r, extended⟩ | ⟨r, inside⟩
    · rcases Run.prefix_snoc pre r (ledger.stops i).pre assigning extended with
        ⟨same, _⟩ | ⟨r', earlier⟩
      · subst same
        obtain rfl := Option.some.inj (before.symm.trans atNext)
        exact absurd unset assigned'
      · rw [← earlier]
        exact firstDown_append pre r' i drop
    · obtain ⟨later, laterFound, life⟩ := r.registryLifecycle.validators i w' atNext
      obtain rfl := Option.some.inj (laterFound.symm.trans before)
      exact absurd ((life.exitEpoch assigned').symm.trans unset) assigned'
  refine (ledger.exactSourceCarrier i).mpr ⟨(Array.getElem?_eq_some_iff.mp initialFound).1,
    reference, ?_, firstDown⟩
  simp [atStop, clean]

/-- This is the assignment premise of the reserved replay of one consolidation request.

It is the form after the approved weakening.

It covers only keys with exit FAR at `s` whose exit is assigned at `t`. -/
def RequestAssigned (rounding : Nat → Nat) {fork : Fork} (s t : BeaconState preset fork)
    (owned : Ownership) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    v.exitEpoch = FAR_FUTURE_EPOCH →
    (∃ w, t.validators.data[i]? = some w ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH) →
    owned.original i ≤ v.effectiveBalance.toNat + rounding i

/-- The block assignment bound at a block input, from the carried bound and the rounding premise.

A key above its effective balance has a positive original.

So it is a new reference key, and it had a first drop. -/
theorem blockAssigned_of_originalDown {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {m n : BeaconState preset fork}
    (pre : Run config checks x ⟨fork, m⟩)
    {epoch : Epoch} {suffix : List PendingConsolidation} {o : Ownership}
    (down : OriginalDown pre o) (reserve : ReserveCut x high ⟨fork, m⟩ epoch suffix o)
    (roundingAt : ∀ (i : Nat) (v w : Validator), m.validators.data[i]? = some v →
      n.validators.data[i]? = some w →
      v.exitEpoch = FAR_FUTURE_EPOCH → w.exitEpoch ≠ FAR_FUTURE_EPOCH →
      NewReference x i → FirstDown pre i →
      rounding i = preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    BlockAssigned rounding m n o := by
  intro i v w found later unset assigned
  have d := down i
  have effective : effectiveAt ⟨fork, m⟩ i = v.effectiveBalance.toNat := by
    simp [effectiveAt, found]
  rw [effective] at d
  by_cases small : o.original i ≤ v.effectiveBalance.toNat
  · omega
  · have ref : NewReference x i := by
      by_contra notReference
      have zero := (reserve.2.2.1 i).2 notReference
      omega
    by_cases f : FirstDown pre i
    · rw [roundingAt i v w found later unset assigned ref f]
      rw [ite_eq_left f] at d
      exact d
    · rw [ite_eq_right f] at d
      omega

/-- Inside a block from `m` to `n`, at a request from `s` to `t`. -/
theorem requestAssigned_of_block {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {m s t n : BeaconState preset fork} {epoch : Epoch}
    {suffix : List PendingConsolidation} {ownedM owned : Ownership}
    (block : BlockAssigned rounding m n ownedM)
    (lifeMS : RegistryLifecycle m s) (kept : EffectiveKept m s) (lifeTN : RegistryLifecycle t n)
    (lower : ∀ i, owned.original i ≤ ownedM.original i)
    (reserve : ReserveCut x high ⟨fork, s⟩ epoch suffix owned)
    (sizeX : x.state.validators.data.size ≤ m.validators.data.size) :
    RequestAssigned rounding s t owned := by
  rintro i v found unset ⟨w, later, assigned⟩
  have l := lower i
  by_cases inside : i < m.validators.data.size
  · have uFound : m.validators.data[i]? = some m.validators.data[i] :=
      Array.getElem?_eq_getElem inside
    obtain ⟨v', vFound, uLife⟩ := lifeMS.validators i _ uFound
    obtain rfl := Option.some.inj (vFound.symm.trans found)
    have uUnset : m.validators.data[i].exitEpoch = FAR_FUTURE_EPOCH := by
      by_contra set
      exact set ((uLife.exitEpoch set).symm.trans unset)
    have same := kept i inside
    simp only [effectiveAt, found, uFound, Option.map_some, Option.getD_some] at same
    obtain ⟨w', wFound, wLife⟩ := lifeTN.validators i w later
    have b := block i _ w' uFound wFound uUnset (by rw [wLife.exitEpoch assigned]; exact assigned)
    omega
  · have none : x.state.validators.data[i]? = none :=
      Array.getElem?_eq_none_iff.mpr (by omega)
    have zero := (reserve.2.2.1 i).1
    simp only [effectiveAt, none, Option.map_none, Option.getD_none] at zero
    omega

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
