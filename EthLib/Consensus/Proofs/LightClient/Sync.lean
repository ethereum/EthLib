module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.LightClient.Sync

/-!
# Proofs: the light client sync protocol

Each error of the light client has its own code.

The ranking of updates is a strict weak order.

It is irreflexive, asymmetric and transitive, and its negation is transitive.

Within one sync committee period, an earlier signature slot beats a later one when the rest matches.

For an optimistic update, the earlier signature slot wins with no hypothesis on the period.

Neither the new update nor the old best update ranks above a kept best valid update.

The finalized and optimistic slots of a store never move back.

A new store starts with one header for both.

The finalized slot then stays at or below the optimistic slot.

An update can make its attested header the optimistic header.

That needs a newer attested header, and more signers than the safety threshold.

That threshold is half the larger of the two counts of signers, rounded down.

An update moves the finalized header only with two thirds of the committee.

The two counts of signers move back a period when such a header opens the next period.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- Two errors with one code come from one constructor. -/
theorem LightClientError.code_injective (e₁ e₂ : LightClientError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [LightClientError.code] at h; exact absurd h (by decide))

/-- A check passes exactly when its condition holds. -/
theorem LightClientError.require_ok {condition : Prop} [Decidable condition]
    {error : LightClientError} {done : Unit} : require condition error = .ok done ↔ condition := by
  unfold require
  split <;> simp_all

/-- A root lifted into the errors of the light client is the root it was. -/
theorem LightClientError.liftRoot_ok {α : Type} {result : Except Err α} {value : α} :
    liftRoot result = .ok value ↔ result = .ok value := by
  cases result <;> simp [liftRoot, Except.mapError]

/-- No update ranks above itself. -/
theorem isBetterUpdate_self {preset : Preset} {fork : Fork}
    (update : LightClientUpdate preset fork) : isBetterUpdate update update = false := by
  simp [isBetterUpdate]

section Order

variable {preset : Preset} {fork : Fork}

/-- One boolean step of the ranking, as a number: `1` for `true`, `0` for `false`. -/
private def boolKey (b : Bool) : Nat := if b then 1 else 0

/-- The ranking key of an update, in the order of the comparison.

A higher key ranks first, so the numeric form reverses the two slots. -/
private def updateRank (update : LightClientUpdate preset fork) : List Nat :=
  let period := computeSyncCommitteePeriodAtSlot preset
  let active := update.syncAggregate.participants
  let supermajority := active * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2
  [boolKey supermajority,
    if supermajority then 0 else active,
    boolKey (update.isSyncCommitteeUpdate &&
      period update.attestedHeader.beacon.slot == period update.signatureSlot),
    boolKey update.isFinalityUpdate,
    boolKey (update.isFinalityUpdate &&
      period update.finalizedHeader.beacon.slot == period update.attestedHeader.beacon.slot),
    active,
    (2 ^ 64 - 1) - update.attestedHeader.beacon.slot.toNat,
    (2 ^ 64 - 1) - update.signatureSlot.toNat]

/-- One step of the tiebreaker: a larger natural key wins, else the tail decides. -/
private theorem step_nat (a b : Nat) (tail : Bool) {xs ys : List Nat}
    (htail : tail = true ↔ ys < xs) :
    (if a ≠ b then decide (a > b) else tail) = true ↔ b :: ys < a :: xs := by
  by_cases hab : a = b
  · subst hab
    simp [htail]
  · simp only [hab, ne_eq, not_false_eq_true, ↓reduceIte, gt_iff_lt, decide_eq_true_eq,
      List.cons_lt_cons_iff, Ne.symm hab, false_and, or_false]

/-- One boolean step of the tiebreaker: `true` beats `false`, else the tail decides. -/
private theorem step_bool (a b tail : Bool) {xs ys : List Nat}
    (htail : tail = true ↔ ys < xs) :
    (if a ≠ b then a else tail) = true ↔ boolKey b :: ys < boolKey a :: xs := by
  cases a <;> cases b <;> simp [boolKey, List.cons_lt_cons_iff, htail]

/-- One slot step of the tiebreaker: an earlier slot wins, else the tail decides. -/
private theorem step_slot (a b : Slot) (tail : Bool) {xs ys : List Nat}
    (htail : tail = true ↔ ys < xs) :
    (if a ≠ b then decide (a < b) else tail) = true ↔
      ((2 ^ 64 - 1) - b.toNat) :: ys < ((2 ^ 64 - 1) - a.toNat) :: xs := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  by_cases hab : a = b
  · subst hab
    simp [htail]
  · have hnat : a.toNat ≠ b.toNat := fun h => hab (UInt64.toNat_inj.mp h)
    have hsub : (2 ^ 64 - 1) - b.toNat ≠ (2 ^ 64 - 1) - a.toNat := by omega
    simp only [hab, ne_eq, not_false_eq_true, ↓reduceIte, UInt64.lt_iff_toNat_lt,
      decide_eq_true_eq, List.cons_lt_cons_iff, hsub, false_and, or_false]
    omega

/-- The final slot comparison, with nothing after it. -/
private theorem last_slot (a b : Slot) :
    decide (a < b) = true ↔
      [(2 ^ 64 - 1) - b.toNat] < [(2 ^ 64 - 1) - a.toNat] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [UInt64.lt_iff_toNat_lt, decide_eq_true_eq, List.cons_lt_cons_iff, and_false,
    or_false, List.not_lt_nil]
  omega

/-- The tiebreaker after finality: signers, attested slot, then signature slot. -/
private def tiebreakTail (na no : Nat) (asn aso ssn sso : Slot) : Bool :=
  if na ≠ no then decide (na > no)
  else if asn ≠ aso then decide (asn < aso)
  else decide (ssn < sso)

private theorem tiebreakTail_eq_lt (na no : Nat) (asn aso ssn sso : Slot) :
    tiebreakTail na no asn aso ssn sso = true ↔
      [no, (2 ^ 64 - 1) - aso.toNat, (2 ^ 64 - 1) - sso.toNat] <
        [na, (2 ^ 64 - 1) - asn.toNat, (2 ^ 64 - 1) - ssn.toNat] :=
  step_nat na no _ (step_slot asn aso _ (last_slot ssn sso))

/-- The comparison of two updates, written on their projected fields. -/
private def betterFields (maxActive na no : Nat) (rn ro fn fo cfn cfo : Bool)
    (asn aso ssn sso : Slot) : Bool :=
  let sn := na * 3 ≥ maxActive * 2
  let so := no * 3 ≥ maxActive * 2
  if sn ≠ so then decide sn
  else if (!decide sn) = true ∧ na ≠ no then decide (na > no)
  else if rn ≠ ro then rn
  else if fn ≠ fo then fn
  else if fn = true then
    if cfn ≠ cfo then cfn
    else tiebreakTail na no asn aso ssn sso
  else tiebreakTail na no asn aso ssn sso

/-- The ranking key of the projected fields, in the order of the comparison. -/
private def fieldRank (maxActive active : Nat) (relevant finality committee : Bool)
    (attested signature : Slot) : List Nat :=
  let supermajority := active * 3 ≥ maxActive * 2
  [boolKey supermajority, if supermajority then 0 else active, boolKey relevant,
    boolKey finality, boolKey (finality && committee), active,
    (2 ^ 64 - 1) - attested.toNat, (2 ^ 64 - 1) - signature.toNat]

private theorem betterFields_eq_lt (maxActive na no : Nat) (rn ro fn fo cfn cfo : Bool)
    (asn aso ssn sso : Slot) :
    betterFields maxActive na no rn ro fn fo cfn cfo asn aso ssn sso = true ↔
      fieldRank maxActive no ro fo cfo aso sso < fieldRank maxActive na rn fn cfn asn ssn := by
  unfold betterFields fieldRank
  have hfin :
      (if fn ≠ fo then fn
        else if fn = true then
          if cfn ≠ cfo then cfn else tiebreakTail na no asn aso ssn sso
        else tiebreakTail na no asn aso ssn sso) = true ↔
      [boolKey fo, boolKey (fo && cfo), no,
          (2 ^ 64 - 1) - aso.toNat, (2 ^ 64 - 1) - sso.toNat] <
        [boolKey fn, boolKey (fn && cfn), na,
          (2 ^ 64 - 1) - asn.toNat, (2 ^ 64 - 1) - ssn.toNat] := by
    cases fn <;> cases fo
    · simpa [boolKey, List.cons_lt_cons_iff] using tiebreakTail_eq_lt na no asn aso ssn sso
    · simp [boolKey, List.cons_lt_cons_iff]
    · simp [boolKey, List.cons_lt_cons_iff]
    · simpa [boolKey, List.cons_lt_cons_iff] using
        step_bool cfn cfo _ (tiebreakTail_eq_lt na no asn aso ssn sso)
  have hrel := step_bool rn ro _ hfin
  by_cases hsn : na * 3 ≥ maxActive * 2 <;> by_cases hso : no * 3 ≥ maxActive * 2
  · simpa [hsn, hso, boolKey, List.cons_lt_cons_iff] using hrel
  · simp [hsn, hso, boolKey, List.cons_lt_cons_iff]
  · simp [hsn, hso, boolKey, List.cons_lt_cons_iff]
  · simpa [hsn, hso, boolKey, List.cons_lt_cons_iff] using step_nat na no _ hrel

/-- A new update ranks above an old one exactly when its ranking key is greater. -/
private theorem isBetterUpdate_eq_rank_lt (newUpdate oldUpdate : LightClientUpdate preset fork) :
    isBetterUpdate newUpdate oldUpdate = true ↔
      updateRank oldUpdate < updateRank newUpdate := by
  simpa only [isBetterUpdate, Id.run, Bind.bind, Pure.pure, updateRank, betterFields,
    tiebreakTail, fieldRank] using
    betterFields_eq_lt preset.SYNC_COMMITTEE_SIZE.toNat
      newUpdate.syncAggregate.participants oldUpdate.syncAggregate.participants
      (newUpdate.isSyncCommitteeUpdate &&
        computeSyncCommitteePeriodAtSlot preset newUpdate.attestedHeader.beacon.slot ==
          computeSyncCommitteePeriodAtSlot preset newUpdate.signatureSlot)
      (oldUpdate.isSyncCommitteeUpdate &&
        computeSyncCommitteePeriodAtSlot preset oldUpdate.attestedHeader.beacon.slot ==
          computeSyncCommitteePeriodAtSlot preset oldUpdate.signatureSlot)
      newUpdate.isFinalityUpdate oldUpdate.isFinalityUpdate
      (computeSyncCommitteePeriodAtSlot preset newUpdate.finalizedHeader.beacon.slot ==
        computeSyncCommitteePeriodAtSlot preset newUpdate.attestedHeader.beacon.slot)
      (computeSyncCommitteePeriodAtSlot preset oldUpdate.finalizedHeader.beacon.slot ==
        computeSyncCommitteePeriodAtSlot preset oldUpdate.attestedHeader.beacon.slot)
      newUpdate.attestedHeader.beacon.slot oldUpdate.attestedHeader.beacon.slot
      newUpdate.signatureSlot oldUpdate.signatureSlot

/-- An update never ranks above one that ranks above it. -/
theorem isBetterUpdate_asymm (a b : LightClientUpdate preset fork)
    (better : isBetterUpdate a b = true) :
    isBetterUpdate b a = false := by
  have hab := (isBetterUpdate_eq_rank_lt a b).mp better
  apply Bool.eq_false_iff.mpr
  intro hba
  exact List.lt_irrefl _ (List.lt_trans hab ((isBetterUpdate_eq_rank_lt b a).mp hba))

/-- An update that ranks above a second, which ranks above a third, ranks above the third. -/
theorem isBetterUpdate_trans {a b c : LightClientUpdate preset fork}
    (ab : isBetterUpdate a b = true) (bc : isBetterUpdate b c = true) :
    isBetterUpdate a c = true :=
  (isBetterUpdate_eq_rank_lt a c).mpr
    (List.lt_trans ((isBetterUpdate_eq_rank_lt b c).mp bc) ((isBetterUpdate_eq_rank_lt a b).mp ab))

/-- Not ranking above another update is transitive. -/
theorem isBetterUpdate_false_trans {a b c : LightClientUpdate preset fork}
    (ab : isBetterUpdate a b = false) (bc : isBetterUpdate b c = false) :
    isBetterUpdate a c = false := by
  apply Bool.eq_false_iff.mpr
  intro ac
  have hab : ¬ updateRank b < updateRank a :=
    fun h => Bool.eq_false_iff.mp ab ((isBetterUpdate_eq_rank_lt a b).mpr h)
  have hbc : ¬ updateRank c < updateRank b :=
    fun h => Bool.eq_false_iff.mp bc ((isBetterUpdate_eq_rank_lt b c).mpr h)
  exact List.not_lt.mpr (List.le_trans (List.not_lt.mp hab) (List.not_lt.mp hbc))
    ((isBetterUpdate_eq_rank_lt a c).mp ac)

/-- An earlier signature in the same sync committee period ranks above a later one. -/
theorem isBetterUpdate_of_signatureSlot_lt {update : LightClientUpdate preset fork}
    {later : Slot} (earlier : update.signatureSlot < later)
    (samePeriod :
      computeSyncCommitteePeriodAtSlot preset update.signatureSlot =
        computeSyncCommitteePeriodAtSlot preset later) :
    isBetterUpdate update { update with signatureSlot := later } = true := by
  rw [isBetterUpdate_eq_rank_lt]
  have hlt := (last_slot update.signatureSlot later).mp (decide_eq_true earlier)
  simpa [updateRank, LightClientUpdate.isSyncCommitteeUpdate, LightClientUpdate.isFinalityUpdate,
    samePeriod, List.cons_lt_cons_iff] using hlt

/-- For an optimistic update, an earlier signature slot always ranks above a later one. -/
theorem LightClientOptimisticUpdate.isBetterUpdate_of_signatureSlot_lt
    {update : LightClientOptimisticUpdate preset fork} {later : Slot}
    (earlier : update.signatureSlot < later) :
    isBetterUpdate update.toUpdate { update with signatureSlot := later }.toUpdate = true := by
  rw [isBetterUpdate_eq_rank_lt]
  have hlt := (last_slot update.signatureSlot later).mp (decide_eq_true earlier)
  have hno : ({ update with signatureSlot := later }.toUpdate).isSyncCommitteeUpdate = false := by
    simp [LightClientOptimisticUpdate.toUpdate, LightClientUpdate.isSyncCommitteeUpdate]
  have hno' : update.toUpdate.isSyncCommitteeUpdate = false := by
    simp [LightClientOptimisticUpdate.toUpdate, LightClientUpdate.isSyncCommitteeUpdate]
  rw [updateRank, updateRank, hno, hno']
  simpa [LightClientOptimisticUpdate.toUpdate, LightClientUpdate.isFinalityUpdate,
    List.cons_lt_cons_iff] using hlt

/-- Neither the processed update nor the old best update ranks above a kept best valid update. -/
theorem processLightClientUpdate_bestValidUpdate {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update best : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after)
    (kept : after.bestValidUpdate = some best) :
    isBetterUpdate update best = false ∧
      ∀ previous, store.bestValidUpdate = some previous →
        isBetterUpdate previous best = false := by
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  cases hold : store.bestValidUpdate with
  | none =>
    rw [hold] at computed
    repeat' split at computed
    all_goals
      cases computed
      try dsimp only at kept
      try contradiction
      try
        rcases Option.some.inj kept with rfl
        exact ⟨isBetterUpdate_self update, fun _ hprev => by cases hprev⟩
  | some old =>
    by_cases hb : isBetterUpdate update old = true
    · rw [hold] at computed
      simp only [hb, ↓reduceIte] at computed
      repeat' split at computed
      all_goals
        cases computed
        try dsimp only at kept
        try contradiction
        try
          rcases Option.some.inj kept with rfl
          refine ⟨isBetterUpdate_self update, fun _ hprev => ?_⟩
          rcases Option.some.inj hprev with rfl
          exact isBetterUpdate_asymm update old hb
    · rw [hold] at computed
      simp only [hb] at computed
      repeat' split at computed
      all_goals
        cases computed
        try dsimp only at kept
        try contradiction
        try
          rw [hold] at kept
          rcases Option.some.inj kept with rfl
          refine ⟨Bool.eq_false_iff.mpr hb, fun _ hprev => ?_⟩
          rcases Option.some.inj hprev with rfl
          exact isBetterUpdate_self old

end Order

section Slots

variable {preset : Preset} {fork : Fork}

/-- A new store starts with one header as both its finalized and its optimistic header.

That header is the header of the bootstrap. -/
theorem initializeLightClientStore_headers {config : Config} {trustedBlockRoot : Root}
    {bootstrap : LightClientBootstrap preset fork} {store : LightClientStore preset fork}
    (computed : initializeLightClientStore config trustedBlockRoot bootstrap = .ok store) :
    store.finalizedHeader = bootstrap.header ∧ store.optimisticHeader = bootstrap.header := by
  unfold initializeLightClientStore at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact ⟨rfl, rfl⟩)

/-- Applying an update never moves either slot back.

It keeps a finalized slot at or below the optimistic slot when it starts there. -/
private theorem applyLightClientUpdate_slots {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork}
    (computed : applyLightClientUpdate store update = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot ∧
      store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot ∧
      (store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot →
        after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot) := by
  unfold applyLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  -- Each branch either fails or rebuilds the store from known headers.
  repeat' split at computed
  all_goals
    cases computed
    try dsimp only
    try refine ⟨?_, ?_, fun _ => ?_⟩
    all_goals
      simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
      omega

/-- Processing an update never moves either slot back.

It keeps a finalized slot at or below the optimistic slot when it starts there. -/
private theorem processLightClientUpdate_slots {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot ∧
      store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot ∧
      (store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot →
        after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot) := by
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- The optimistic header only moves to a later attested header before the update applies.
  repeat' split at computed
  all_goals
    try have applied := applyLightClientUpdate_slots ‹applyLightClientUpdate _ _ = .ok _›
    cases computed
    try dsimp only at *
    try refine ⟨?_, ?_, fun _ => ?_⟩
    all_goals
      simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
      omega

/-- A forced update never moves either slot back.

It keeps a finalized slot at or below the optimistic slot when it starts there. -/
private theorem processLightClientStoreForceUpdate_slots
    {store after : LightClientStore preset fork} {currentSlot : Slot}
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot ∧
      store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot ∧
      (store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot →
        after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot) := by
  unfold processLightClientStoreForceUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  repeat' split at computed
  all_goals
    try have applied := applyLightClientUpdate_slots ‹applyLightClientUpdate _ _ = .ok _›
    cases computed
    try dsimp only at *
    try refine ⟨?_, ?_, fun _ => ?_⟩
    all_goals
      simp only [gt_iff_lt, UInt64.le_iff_toNat_le] at *
      omega

/-- Applying an update never moves the finalized slot back. -/
theorem applyLightClientUpdate_finalizedSlot_le {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork}
    (computed : applyLightClientUpdate store update = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot :=
  (applyLightClientUpdate_slots computed).1

/-- Applying an update never moves the optimistic slot back. -/
theorem applyLightClientUpdate_optimisticSlot_le {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork}
    (computed : applyLightClientUpdate store update = .ok after) :
    store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot :=
  (applyLightClientUpdate_slots computed).2.1

/-- Applying an update keeps a finalized slot at or below the optimistic slot. -/
theorem applyLightClientUpdate_slot_order {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork}
    (computed : applyLightClientUpdate store update = .ok after)
    (ordered : store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot) :
    after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot :=
  (applyLightClientUpdate_slots computed).2.2 ordered

/-- Processing an update never moves the finalized slot back. -/
theorem processLightClientUpdate_finalizedSlot_le {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot :=
  (processLightClientUpdate_slots computed).1

/-- Processing an update never moves the optimistic slot back. -/
theorem processLightClientUpdate_optimisticSlot_le {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot :=
  (processLightClientUpdate_slots computed).2.1

/-- Processing an update keeps a finalized slot at or below the optimistic slot. -/
theorem processLightClientUpdate_slot_order {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after)
    (ordered : store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot) :
    after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot :=
  (processLightClientUpdate_slots computed).2.2 ordered

/-- A forced update never moves the finalized slot back. -/
theorem processLightClientStoreForceUpdate_finalizedSlot_le
    {store after : LightClientStore preset fork} {currentSlot : Slot}
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot :=
  (processLightClientStoreForceUpdate_slots computed).1

/-- A forced update never moves the optimistic slot back. -/
theorem processLightClientStoreForceUpdate_optimisticSlot_le
    {store after : LightClientStore preset fork} {currentSlot : Slot}
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after) :
    store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot :=
  (processLightClientStoreForceUpdate_slots computed).2.1

/-- A forced update keeps a finalized slot at or below the optimistic slot. -/
theorem processLightClientStoreForceUpdate_slot_order
    {store after : LightClientStore preset fork} {currentSlot : Slot}
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after)
    (ordered : store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot) :
    after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot :=
  (processLightClientStoreForceUpdate_slots computed).2.2 ordered

end Slots

section Headers

variable {preset : Preset} {fork : Fork}

/-- No more members sign than the sync committee has. -/
theorem SyncAggregate.participants_le (aggregate : SyncAggregate preset) :
    aggregate.participants ≤ preset.SYNC_COMMITTEE_SIZE.toNat := by
  unfold SyncAggregate.participants
  simpa using List.count_le_length (a := true) (l := aggregate.syncCommitteeBits.bits.toList)

/-- Applying an update takes a newer finalized header, and as optimistic header if newer still.

At a new period with the next committee known, the current count becomes the previous one.

The current count then starts again at zero. -/
private theorem applyLightClientUpdate_fields {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork}
    (computed : applyLightClientUpdate store update = .ok after) :
    let finalized := update.finalizedHeader
    let newer := finalized.beacon.slot > store.finalizedHeader.beacon.slot
    let rotated := store.isNextSyncCommitteeKnown = true ∧
      computeSyncCommitteePeriodAtSlot preset finalized.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1
    after.finalizedHeader = (if newer then finalized else store.finalizedHeader) ∧
      after.optimisticHeader =
        (if newer ∧ finalized.beacon.slot > store.optimisticHeader.beacon.slot then finalized
          else store.optimisticHeader) ∧
      after.currentMaxActiveParticipants =
        (if rotated then 0 else store.currentMaxActiveParticipants) ∧
      after.previousMaxActiveParticipants =
        (if rotated then store.currentMaxActiveParticipants
          else store.previousMaxActiveParticipants) := by
  unfold applyLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  repeat' split at computed
  all_goals
    cases computed
    try dsimp only
    try simp_all [← UInt64.not_le]

/-- After an update, both headers and both counts of signers take the values of the protocol.

The current count first takes the signers of the update, if they are more.

The optimistic header becomes the attested header if it is newer and more than the threshold signed.

That threshold is half the larger of the previous count and the current count, rounded down.

With two thirds of the committee, a newer finalized header replaces the finalized header.

It also replaces the optimistic header if it is newer than that one.

If it opens the next period while the next committee is known, the counts move back a period. -/
private theorem processLightClientUpdate_fields {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    let active := update.syncAggregate.participants
    let current := max store.currentMaxActiveParticipants.toNat active
    let optimistic :=
      if active > max store.previousMaxActiveParticipants.toNat current / 2 ∧
          update.attestedHeader.beacon.slot > store.optimisticHeader.beacon.slot then
        update.attestedHeader
      else store.optimisticHeader
    let finalized := update.finalizedHeader
    let newer := active * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2 ∧
      finalized.beacon.slot > store.finalizedHeader.beacon.slot
    let rotated := newer ∧ store.isNextSyncCommitteeKnown = true ∧
      computeSyncCommitteePeriodAtSlot preset finalized.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1
    after.finalizedHeader = (if newer then finalized else store.finalizedHeader) ∧
      after.optimisticHeader =
        (if newer ∧ finalized.beacon.slot > optimistic.beacon.slot then finalized
          else optimistic) ∧
      after.currentMaxActiveParticipants.toNat = (if rotated then 0 else current) ∧
      after.previousMaxActiveParticipants.toNat =
        (if rotated then current else store.previousMaxActiveParticipants.toNat) := by
  have small : update.syncAggregate.participants < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (SyncAggregate.participants_le _) (UInt64.toNat_lt _)
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals
    try have applied := applyLightClientUpdate_fields ‹applyLightClientUpdate _ _ = .ok _›
    cases computed
    try dsimp only at *
    try simp_all [LightClientStore.safetyThreshold, LightClientStore.isNextSyncCommitteeKnown,
      Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt small, Base.Uint64.toNat_max,
      apply_ite UInt64.toNat, ← UInt64.not_le]
  all_goals
    repeat' split
    all_goals simp_all

/-- After an update, the optimistic header is the attested header if more than the threshold signed.

That also needs the attested header to be newer than the optimistic header.

The threshold is half the larger of the previous count and the current count, rounded down.

The current count has first taken the signers of the update, if they are more.

Otherwise the optimistic header stays.

With two thirds of the committee, a newer finalized header replaces it if that is newer still. -/
theorem processLightClientUpdate_optimisticHeader {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    let active := update.syncAggregate.participants
    let optimistic :=
      if active > max store.previousMaxActiveParticipants.toNat
            (max store.currentMaxActiveParticipants.toNat active) / 2 ∧
          update.attestedHeader.beacon.slot > store.optimisticHeader.beacon.slot then
        update.attestedHeader
      else store.optimisticHeader
    after.optimisticHeader =
      if active * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2 ∧
          update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot ∧
          update.finalizedHeader.beacon.slot > optimistic.beacon.slot then
        update.finalizedHeader
      else optimistic := by
  have fields := (processLightClientUpdate_fields computed).2.1
  simp only [and_assoc] at fields
  exact fields

/-- After an update, the finalized header is its finalized header if that is newer.

That needs two thirds of the committee to sign; otherwise the finalized header stays. -/
theorem processLightClientUpdate_finalizedHeader {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.finalizedHeader =
      if update.syncAggregate.participants * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2 ∧
          update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot then
        update.finalizedHeader
      else store.finalizedHeader :=
  (processLightClientUpdate_fields computed).1

/-- After an update, the current count of signers first takes the signers of the update, if more.

The counts then move back a period when a newer finalized header falls in the next period.

That needs two thirds of the committee, and a store that knows the next committee.

The previous count then takes that larger count, and the current count is zero. -/
theorem processLightClientUpdate_maxActiveParticipants {config : Config}
    {checks : SignatureChecks} {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    let active := update.syncAggregate.participants
    let current := max store.currentMaxActiveParticipants.toNat active
    let rotated := active * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2 ∧
      update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot ∧
      store.isNextSyncCommitteeKnown = true ∧
      computeSyncCommitteePeriodAtSlot preset update.finalizedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1
    after.currentMaxActiveParticipants.toNat = (if rotated then 0 else current) ∧
      after.previousMaxActiveParticipants.toNat =
        (if rotated then current else store.previousMaxActiveParticipants.toNat) := by
  have fields := (processLightClientUpdate_fields computed).2.2
  simp only [and_assoc] at fields
  exact fields

end Headers

end EthLib.Consensus
